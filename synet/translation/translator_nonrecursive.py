from logicblox_grammar import parse_logicblox
import z3
from string import ascii_uppercase
from constant import Constant
from lib2to3.pgen2 import literals

DISTINCT_CONSTRAINT = True
BIT_VEC_SIZE = 1 # for encoding string constants
LB_TYPE_TO_Z3_TYPE = {}
(VERTEX, x) = z3.EnumSort('Vertex', ['R1']) # link with the synthesizer type for VERTEX
LB_TYPE_TO_Z3_TYPE['Vertex'] = VERTEX
LB_TYPE_TO_Z3_TYPE['string'] = z3.BitVecSort(BIT_VEC_SIZE)
LB_TYPE_TO_Z3_TYPE['int'] = z3.IntSort()

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


class Translator:  

  def __init__(self, logicblox_filename, unroll_limit):
    self.unroll_limit = unroll_limit
    self.program = parse_logicblox(logicblox_filename)  
    self.fresh_vars_index = 0
    self.fresh_vars = []
    self.recursive_idb_predicate_names = self.program.get_recursive_idb_predicate_names()
    self.nonrecursive_idb_predicate_names = self.program.get_nonrecursive_idb_predicate_names()
    self.declare_predicates()
  
  def get_pos_predicate_name(self, predicate_name):
    return predicate_name + '_unrolled'
  
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
        pos_predicate_name = self.get_pos_predicate_name(predicate_name)
        self.predicates[pos_predicate_name] = z3.Function(*([pos_predicate_name] + term_types + [z3.BoolSort()]))          
      
  def get_predicate(self, predicate_name, step_index):
    assert step_index <= self.unroll_limit
    if predicate_name not in self.recursive_idb_predicate_names:
      return self.predicates[predicate_name]
    else:
      pos_predicate_name = self.get_pos_predicate_name(predicate_name)
      return self.predicates[pos_predicate_name]
    
  def get_fresh_var(self, fresh_var_sort):
    if not self.fresh_vars:      
      self.fresh_vars = [ascii_uppercase[-i-1] + str(self.fresh_vars_index) for i in range(len(ascii_uppercase))]
      self.fresh_vars_index += 1
    return z3.Const(self.fresh_vars.pop(), fresh_var_sort)
  
  def reset_fresh_vars(self):
    self.fresh_vars = []
    self.fresh_vars_index = 0
  
  def to_z3(self):
    z3_constraints = []
    for predicate_name in self.program.get_idb_predicate_names():
      self.reset_fresh_vars()
      predicate = self.get_predicate(predicate_name, self.unroll_limit)
      z3_head_vars = []
      for var_id in range(predicate.arity()):
        z3_fresh_var = self.get_fresh_var(predicate.domain(var_id))
        z3_head_vars.append(z3_fresh_var) 
      (z3_body_free_vars, z3_body_constraint) = self.pred_to_z3(predicate_name, self.unroll_limit, z3_head_vars)
      if DISTINCT_CONSTRAINT:
        vertex_variables = [var for var in z3_head_vars + z3_body_free_vars if var.sort() == VERTEX]
        if vertex_variables:
          z3_body_constraint = z3.And(z3.Distinct(vertex_variables), z3_body_constraint)
      z3_constraint = z3.ForAll(z3_head_vars, predicate(z3_head_vars) == (z3_body_constraint if len(z3_body_free_vars) == 0 else z3.Exists(z3_body_free_vars, z3_body_constraint)))
      z3_constraints.append(z3_constraint)
    return z3_constraints

  def pred_to_z3(self, predicate_name, step_index, z3_head_vars):
    assert predicate_name in self.program.get_idb_predicate_names()
          
    z3_bodies = []
    z3_body_free_vars = []
    # Encode all rule bodies into Z3
    for rule in self.program.get_rules_for_predicate(predicate_name):            
      
      skip_rule = False
      for literal in rule.get_literals():
        if literal.atom.name in self.program.get_recursive_idb_predicate_names() and step_index == 1:
          skip_rule = True
      if skip_rule:
        continue
          
      substitution = {}
      for var_index in range(len(z3_head_vars)):
        substitution[rule.head.get_vars()[var_index]] = z3_head_vars[var_index]
             
      z3_body_constraints = []      
      # Keep track of all free variables in the body (which are existentially quantified later)      
      
      # Encode all literals that appear in the body
      for literal in rule.get_literals():
        literal_predicate = self.get_predicate(literal.atom.name, step_index)
        z3_literal_vars = []
        for literal_var_index in range(len(literal.get_vars())):
          literal_var = literal.get_vars()[literal_var_index]
          if literal_var.wildcard: # e.g. Node(_, ..)
              z3_fresh_var = self.get_fresh_var(literal_predicate.domain(literal_var_index))
              z3_body_free_vars.append(z3_fresh_var)            
              z3_literal_vars.append(z3_fresh_var)
          elif literal_var in substitution.keys():
            z3_literal_vars.append(substitution[literal_var])
          else:
            z3_fresh_var = self.get_fresh_var(literal_predicate.domain(literal_var_index))
            substitution[literal_var] = z3_fresh_var
            z3_body_free_vars.append(z3_fresh_var)
            z3_literal_vars.append(z3_fresh_var)
        if literal.atom.name in self.program.get_edb_predicate_names() or literal.atom.name in self.program.get_nonrecursive_idb_predicate_names():
          if literal.negated:        
            z3_body_constraints.append(z3.Not(literal_predicate(z3_literal_vars)))
          else:
            z3_body_constraints.append(literal_predicate(z3_literal_vars))        
        else:          
          if step_index > 1:        
            (tmp_free_vars, body_constraint) = self.pred_to_z3(literal.atom.name, step_index - 1, z3_literal_vars)
            z3_body_free_vars = z3_body_free_vars + tmp_free_vars
            z3_body_constraints.append(body_constraint)
          else:
            z3_body_constraints.append(False)
             

      # Encode all comparisons that appear in the body (e.g. cost = cost1 + cost2)
      for comparison in rule.get_comparisons():
        # Assume all variables that appear in comparisons are bound to literals
        z3_left = substitution[comparison.left]
        z3_right_terms = []
        for right_term in comparison.right.get_terms():
          if right_term.is_variable:
            z3_right_terms.append(substitution[right_term])
          elif right_term.is_constant and right_term.type == Constant.INTEGER_CONSTANT:
            z3_right_terms.append(right_term.value)
          elif right_term.is_constant and right_term.type == Constant.STRING_CONSTANT:
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
      z3_bodies.append(z3_body_constraints_conjunction)
      
    # Construct the Z3 constraint for the current predicate 
    z3_constraint = z3.Or(z3_bodies) if len(z3_bodies) > 1 else z3_bodies[0]
    return (z3_body_free_vars, z3_constraint)
      
if __name__ == '__main__':
  unroll_limit = 3
  box = Translator('../../logicblox/stratum-02-ospf-01.logic', unroll_limit)
  #box = Translator('../../logicblox/recursive_test.logic', unroll_limit)
  print box.to_z3()
