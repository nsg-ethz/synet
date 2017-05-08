class Literal:
  def __init__(self, parsed_tokens):
    self.is_literal = True
    if parsed_tokens[0] == '!':
      self.negated = True
      self.atom = parsed_tokens[1]
    else:
      self.negated = False
      self.atom = parsed_tokens[0]
      
  def __str__(self):
    if self.negated:
      return '!' + str(self.atom)
    else:
      return str(self.atom)
    
  def get_terms(self):
    return self.atom.get_terms()
  
  def get_vars(self):
    return self.atom.get_vars()
    
def parse_literal(parsed_tokes):
  return Literal(parsed_tokes)