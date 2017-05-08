class Variable:
  def __init__(self, name):
    self.name = name
    self.is_variable = True
    self.is_constant = False
    if self.name == '_':
      self.wildcard = True
    else:
      self.wildcard = False
      
  def __str__(self):
    return self.name

  def __eq__(self, other):    
    if isinstance(other, self.__class__):
      return self.name == other.name
    else:
      return False
    
  def __hash__(self):
    return hash(self.name)
  
def parse_variable(parsed_tokens):
  return Variable(parsed_tokens[0])