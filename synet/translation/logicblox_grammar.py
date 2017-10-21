from pyparsing import Word, nums
from pyparsing import Optional
from pyparsing import restOfLine
from pyparsing import ZeroOrMore
from pyparsing import OneOrMore
from pyparsing import Group
from pyparsing import alphanums
from pyparsing import Literal
from pyparsing import Regex

from atom import parse_atom
from literal import parse_literal
from rule import parse_rule
from arithmetic_expression import parse_arithmetic_expr
from comparison_expression import parse_comp_expr
from variable import parse_variable
from constant import parse_constant
from program import Program

predicate_name = Regex(r'[a-zA-Z][a-zA-Z0-9_]*')
variable_name = Regex(r'[a-zA-Z_][a-zA-Z0-9_]*').setParseAction(parse_variable)
string_constant = Regex(r'"[a-zA-Z0-9\_\-]+:[a-zA-Z0-9\_\-]+"').setParseAction(parse_constant)
integer_constant = Word(nums).setParseAction(parse_constant)
constant = string_constant | integer_constant
term = variable_name | constant
leftarrow = Literal('<-')
rightarrow = Literal('->')
leftbracket = Literal('(').suppress()
rightbracket = Literal(')').suppress()
comma = Literal(',').suppress()
negation = Literal('!')
dot = Literal('.').suppress()
comment = Group(Literal('//') + restOfLine).suppress()
plus = Literal('+')
eq = Literal('=')
neq = Literal('!=')
lt = Literal('<')
gt = Literal('>')
colon = Literal(':')
leq = Literal('<=')
geq = Literal('>=')
comp = eq | neq | lt | gt | leq | geq

atom = (predicate_name + leftbracket + Group(ZeroOrMore(Optional(comma) + term)) + rightbracket).setParseAction(parse_atom)
standard_literal = (Optional(negation) + atom).setParseAction(parse_literal)
arithmetic_expr = (term + ZeroOrMore(plus + term)).setParseAction(parse_arithmetic_expr) # for now we handle only addition 
comp_expr = (term + comp + arithmetic_expr).setParseAction(parse_comp_expr)
literal = standard_literal | comp_expr
rule = (atom + leftarrow + Group(Optional(literal) + ZeroOrMore(comma + literal)) + dot).setParseAction(parse_rule)
type_rule = (atom + rightarrow + Group(Optional(literal) + ZeroOrMore(comma + literal)) + dot).setParseAction(parse_rule)
program = OneOrMore(comment | type_rule | rule)

def parse_logicblox(filename):
  parsed_rules = program.parseFile(filename, parseAll=True)
  rules = [x for x in parsed_rules]
  return Program(rules)
