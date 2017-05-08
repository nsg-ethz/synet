class Atom:
  def __init__(self, parsed_tokens):
    self.name = parsed_tokens[0]
    self.terms = [term for term in parsed_tokens[1]]    
    
  def __str__(self):
    return self.name + '(' + ', '.join([str(term) for term in self.terms]) + ')'
  
  def get_terms(self):
    return self.terms 
  
  def get_vars(self):
    return [term for term in self.terms if term.is_variable]
  
  def get_constants(self):
    return [term for term in self.terms if term.is_constant]
  
def parse_atom(parsed_tokes):
  return Atom(parsed_tokes)