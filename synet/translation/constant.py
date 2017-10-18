class Constant:
  
  INTEGER_CONSTANT = 'INTEGER'
  STRING_CONSTANT = 'STRING'
  NODE_CONSTANT = 'NODE'
  IFACE_CONSTANT = 'IFACE'
  NET_CONSTANT = 'NET'
  
  def __init__(self, value):
    self.is_constant = True
    self.is_variable = False
    
    if value.isdigit():
      self.type = Constant.INTEGER_CONSTANT
      self.value = int(value)
    elif value.startswith('"'):
      self.type = value[1:-1].split('_')[0] #  Constant.STRING_CONSTANT
      self.value = value[1:-1].split('_')[1]
    else:
      raise NameError('Unknown constant type: {}'.format(value))
      
  def __str__(self):
    return str(self.value)
  
  def __eq__(self, other):    
    if isinstance(other, self.__class__):
      return self.value == other.value and self-type == other.type
    else:
      return False
    
  def __hash__(self):
    return hash((self.type, self.value))
    
def parse_constant(parsed_tokens):  
  return Constant(parsed_tokens[0])
