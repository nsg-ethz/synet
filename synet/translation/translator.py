from logicblox_grammar import parse_logicblox
import z3
from string import ascii_uppercase
from constant import Constant

BIT_VEC_SIZE = 5 # for encoding string constants
LB_TYPE_TO_Z3_TYPE = {}
(NODE, x) = z3.EnumSort('Node', ['R1']) # link with the synthesizer type for network node
(IFACE, x) = z3.EnumSort('Interface', ['I1']) # link with the synthesizer type for interface
(NET, x) = z3.EnumSort('Network', ['N1']) # link with the synthesizer type for network

LB_TYPE_TO_Z3_TYPE['Node'] = NODE
LB_TYPE_TO_Z3_TYPE['Interface'] = IFACE
LB_TYPE_TO_Z3_TYPE['Network'] = NET
LB_TYPE_TO_Z3_TYPE['string'] = z3.BitVecSort(BIT_VEC_SIZE)
LB_TYPE_TO_Z3_TYPE['int'] = z3.IntSort()

STRING_TO_NODE = {'R1': z3.Const('R1', NODE)}
STRING_TO_IFACE = {'I1': z3.Const('I1', IFACE)}
STRING_TO_NET = {'N1': z3.Const('N1', NET)}
STRING_TO_BITVAL = {}


def get_string_const_val(string):
  if string in STRING_TO_BITVAL.keys():
    return STRING_TO_BITVAL[string]

  if 2 ** BIT_VEC_SIZE < len(STRING_TO_BITVAL.keys()):
    raise NameError(
      'Cannot encode all strings with {} bits'.format(BIT_VEC_SIZE))
  STRING_TO_BITVAL[string] = z3.BitVecVal(len(STRING_TO_BITVAL.keys()),
                                          BIT_VEC_SIZE)
  return STRING_TO_BITVAL[string]


get_string_const_val('static')
get_string_const_val('ospf')
get_string_const_val('bgp')
get_string_const_val('1;2;3')


class Translator:  

  def __init__(self, logicblox_filename, unroll_limit):
    self.unroll_limit = unroll_limit
    self.program = parse_logicblox(logicblox_filename)
    self.recursive_idb_predicate_names = self.program.get_recursive_idb_predicate_names()
    self.nonrecursive_idb_predicate_names = self.program.get_nonrecursive_idb_predicate_names()
    self.declare_predicates()
  
  def get_ith_step_predicate_name(self, predicate_name, step_index):
    return predicate_name + '_' + str(step_index)
  
  def declare_predicates(self):
    self.predicates = {}
    for type_rule in self.program.get_type_rules():
      predicate_name = type_rule.head.name
      term_types = []
      for var in type_rule.head.get_vars():
        for literal in type_rule.get_literals():          
          assert not literal.negated
          assert len(literal.get_vars()) == 1
          literal_var = literal.get_vars()[0]
          if var == literal_var:
            term_types.append(LB_TYPE_TO_Z3_TYPE[literal.atom.name])
      self.predicates[predicate_name] = z3.Function(*([predicate_name] + term_types + [z3.BoolSort()]))
      if predicate_name in self.recursive_idb_predicate_names:
        for step_index in range(self.unroll_limit + 1):
          ith_step_predicate_name = self.get_ith_step_predicate_name(predicate_name, step_index)
          self.predicates[ith_step_predicate_name] = z3.Function(*([ith_step_predicate_name] + term_types + [z3.BoolSort()]))          
      
  def get_predicate(self, predicate_name, step_index):
    if step_index > self.unroll_limit or predicate_name not in self.recursive_idb_predicate_names:
      return self.predicates[predicate_name]
    else:
      ith_step_predicate_name = self.get_ith_step_predicate_name(predicate_name, step_index)
      return self.predicates[ith_step_predicate_name]

  def to_z3(self):
    z3_constraints = []
    for predicate_name in self.program.get_idb_predicate_names():
      for step_index in range(self.unroll_limit) + [self.unroll_limit + 1]:       
        predicate = self.get_predicate(predicate_name, step_index + 1)
        #var_names = [ascii_uppercase[-i-1] for i in range(len(ascii_uppercase))]
        var_names = ['VAR%d' % i for i in range(2000)]
        
        z3_head_vars = []
        for var_id in range(predicate.arity()):
          z3_head_vars.append(z3.Const(var_names.pop(), predicate.domain(var_id)))
        # Declare the head Z3 predicate (e.g. node(X) == ...)
        z3_head = predicate(z3_head_vars)
          
        z3_bodies = []
        # Encode all rule bodies into Z3
        for rule in self.program.get_rules_for_predicate(predicate_name):
          lb_vars_to_z3_vars = {}        
          # Consistently substitute all variables that appear in the head
          for arg_id in range(len(z3_head_vars)):
            lb_vars_to_z3_vars[rule.head.get_vars()[arg_id]] = z3_head_vars[arg_id]
                  
          z3_body_constraints = []
          
          # Keep track of all free variables in the body (which are existentially quantified later)
          z3_body_free_vars = []
          
          # Encode all literals that appear in the body
          for literal in rule.get_literals():            
            literal_predicate = self.get_predicate(literal.atom.name, step_index)            
            z3_body_vars = []
            for body_var_index in range(len(literal.get_vars())):
              body_var = literal.get_vars()[body_var_index]
              if body_var.wildcard: # e.g. Node(_, ..)
                z3_fresh_var = z3.Const(var_names.pop(), literal_predicate.domain(body_var_index))
                z3_body_free_vars.append(z3_fresh_var)            
                z3_body_vars.append(z3_fresh_var)
              else:
                if body_var not in lb_vars_to_z3_vars.keys():
                  # Declare a fresh variable if it does not appear in the head     
                  z3_fresh_var = z3.Const(var_names.pop(), literal_predicate.domain(body_var_index))
                  z3_body_free_vars.append(z3_fresh_var)      
                  lb_vars_to_z3_vars[body_var] = z3_fresh_var
                z3_body_vars.append(lb_vars_to_z3_vars[body_var])
            if literal.atom.name in self.recursive_idb_predicate_names and step_index == 0:
              z3_body_constraints.append(False)
              continue
            if literal.negated:  
              z3_body_constraints.append(z3.Not(literal_predicate(z3_body_vars)))
            else:
              z3_body_constraints.append(literal_predicate(z3_body_vars))
  
          # Encode all comparisons that appear in the body (e.g. cost = cost1 + cost2)
          for comparison in rule.get_comparisons():
            # Assume all variables that appear in comparisons are bound to literals
            z3_left = lb_vars_to_z3_vars[comparison.left]
            z3_right_terms = []
            for right_term in comparison.right.get_terms():
              if right_term.is_variable:
                z3_right_terms.append(lb_vars_to_z3_vars[right_term])
              elif right_term.is_constant and right_term.type == Constant.INTEGER_CONSTANT:
                z3_right_terms.append(right_term.value)
              elif right_term.is_constant and right_term.type == Constant.NODE_CONSTANT and right_term.value in STRING_TO_NODE.keys():
                z3_right_terms.append(STRING_TO_NODE[right_term.value])
              elif right_term.is_constant and right_term.type == Constant.IFACE_CONSTANT and right_term.value in STRING_TO_IFACE.keys():
                z3_right_terms.append(STRING_TO_IFACE[right_term.value])
              elif right_term.is_constant and right_term.type == Constant.NET_CONSTANT and right_term.value in STRING_TO_NET.keys():
                z3_right_terms.append(STRING_TO_NET[right_term.value])
              elif right_term.is_constant and right_term.type == Constant.NODE_CONSTANT and right_term.value not in STRING_TO_NODE.keys() + STRING_TO_NET.keys() + STRING_TO_IFACE.keys():
                z3_right_terms.append(get_string_const_val(right_term.value))
              else:
                raise NameError('Unknown term: {}'.format(right_term))             
            if comparison.right.is_atomic:
              z3_right = z3_right_terms[0]
            else:
              if comparison.right.op == '+':
                z3_right = reduce(lambda x, y: x + y, z3_right_terms)
              else:
                raise NameError('Add support for arithmetic expressions of type {}'.format(comparison.right.op))
            if comparison.op == '<':
              z3_comparison = z3_left < z3_right              
            elif comparison.op == '=':
                z3_comparison = z3_left == z3_right
            elif comparison.op == '!=':
              z3_comparison = z3_left != z3_right
            else:
              raise NameError('Add support for comparisons of type {}'.format(comparison.op))
            z3_body_constraints.append(z3_comparison)
          
          # Get the conjunction of all z3 body constraints
          if len(z3_body_constraints) == 1:
            z3_body_constraints_conjunction = z3_body_constraints[0]          
          else:
            z3_body_constraints_conjunction = z3.And(z3_body_constraints)
          # Quantify free variables (if any)  
          if len(z3_body_free_vars) == 0:
            z3_body = z3_body_constraints_conjunction          
          else:
            z3_body = z3.Exists(z3_body_free_vars, z3_body_constraints_conjunction)
                    
          z3_bodies.append(z3_body)
          
        # Construct the Z3 constraint for the current predicate 
        z3_constraint = z3.ForAll(z3_head_vars, z3_head == z3.Or(z3_bodies)) if len(z3_bodies) > 1 else z3.ForAll(z3_head_vars, predicate(z3_head_vars) == z3_bodies[0])
        
        z3_constraints.append(z3_constraint)
        if predicate_name in self.nonrecursive_idb_predicate_names:
          break
    return z3_constraints
      
if __name__ == '__main__':
  unroll_limit = 2
  box = Translator('synet/datalog/types.logic', unroll_limit)
    
  print box.to_z3()
