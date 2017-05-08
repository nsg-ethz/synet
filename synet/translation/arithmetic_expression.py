class ArithmeticExpression(object):

  def __init__(self, parsed_tokens):    
    if len(parsed_tokens) == 1:
      self.is_atomic = True
    else:
      self.is_atomic = False
      self.op = parsed_tokens[1]
    self.args = parsed_tokens[0::2]
    
  def __str__(self):
    if self.is_atomic:
      return str(self.args[0])
    else:
      return ' {} '.format(self.op).join(str(arg) for arg in self.args)
    
  def get_terms(self):
    return self.args
  
def parse_arithmetic_expr(parsed_tokens):
  return ArithmeticExpression(parsed_tokens)
