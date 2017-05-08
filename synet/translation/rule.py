class Rule:
  def __init__(self, parsed_tokens):
    self.head = parsed_tokens[0]
    if parsed_tokens[1] == '->':
      self.is_type_rule = True
    else:
      self.is_type_rule = False      
    self.body = parsed_tokens[2]
    if not self.is_type_rule:
      self.sanity_checks()

  def sanity_checks(self):
    body_vars = [str(var) for var in self.get_body_vars() + self.get_comparisons_vars()]
    for head_var in [str(var) for var in self.head.get_vars()]:
      assert head_var in body_vars
    for body_free_var in [str(var) for var in self.get_body_free_vars()]:
      if body_free_var == '_' or body_free_var.startswith('cost'):
        continue
      occurances_of_body_free_var = 0
      for literal in self.body:
        if body_free_var in [str(var) for var in literal.get_vars()]:
          occurances_of_body_free_var += 1
      assert occurances_of_body_free_var > 1
    

  def __str__(self):
    if self.is_type_rule:
      arrow = ' -> '
    else:
      arrow = ' <- '
    return str(self.head) +  arrow + ', '.join([str(lit) for lit in self.body])
  
  def get_literals(self):
    return [arg for arg in self.body if arg.is_literal]
  
  def get_comparisons(self):
    return [arg for arg in self.body if not arg.is_literal]
  
  def get_head_vars(self):
    return self.head.get_vars()
  
  def get_body_vars(self):
    body_vars = []
    for literal in self.get_literals():
      body_vars = body_vars + literal.get_vars()
    return body_vars
  
  def get_comparisons_vars(self):
    comp_vars = []
    for comparison in self.get_comparisons():
      comp_vars = comp_vars + comparison.get_vars()
    return comp_vars
  
  def get_body_free_vars(self):
    return [var for var in self.get_body_vars() if var not in self.get_head_vars()]
  
def parse_rule(parsed_tokens):
  return Rule(parsed_tokens)
