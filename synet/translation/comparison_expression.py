class ComparisonExpression(object):

  def __init__(self, parsed_tokens):
    assert(len(parsed_tokens) > 1)
    self.is_literal = False
    self.left = parsed_tokens[0]
    self.op = parsed_tokens[1]
    self.right = parsed_tokens[2]
  
  def __str__(self):
    return '{} {} {}'.format(str(self.left), str(self.op), str(self.right))
  
  def get_vars(self):
    return [self.left, self.right]

def parse_comp_expr(parsed_tokens):
  return ComparisonExpression(parsed_tokens)
