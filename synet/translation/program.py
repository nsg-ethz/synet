from networkx.classes.digraph import DiGraph
from networkx.algorithms.components.strongly_connected import strongly_connected_components
from networkx.algorithms.cycles import simple_cycles
from networkx.algorithms.shortest_paths.generic import has_path

class Program:
  def __init__(self, rules):
    self.rules = rules
    self.predicate_names = None
    self.predicate_deps_graph = None
    assert(self.is_stratified())
  
  def get_rules(self):
    return self.rules
  
  def get_derivation_rules(self):
    return [rule for rule in self.rules if not rule.is_type_rule]
  
  def get_type_rules(self):
    return [rule for rule in self.rules if rule.is_type_rule]
  
  def get_predicate_names(self):
    if self.predicate_names != None:
      return self.predicate_names
    
    self.predicate_names = set()
    for rule in self.get_derivation_rules():
      self.predicate_names.add(rule.head.name)
      for literal in rule.get_literals():
        self.predicate_names.add(literal.atom.name)
    return self.predicate_names
  
  def get_nonrecursive_idb_predicate_names(self):
    return self.extend_nonrecursive_idb_predicate_names(set())
  
  def get_recursive_idb_predicate_names(self):
    return self.get_idb_predicate_names() - self.get_nonrecursive_idb_predicate_names()
  
  def extend_nonrecursive_idb_predicate_names(self, cur_nonrecursive):
    extended_nonrecursive = set()
    for predicate_name in self.get_idb_predicate_names():
      if predicate_name in cur_nonrecursive:
        extended_nonrecursive.add(predicate_name)
        continue
      
      recursive = False
      for rule in self.get_rules_for_predicate(predicate_name):
        for literal in rule.get_literals():
          literal_predicate_name = literal.atom.name
          if literal_predicate_name not in self.get_edb_predicate_names() and literal_predicate_name not in cur_nonrecursive:
            recursive = True
      if not recursive:
        extended_nonrecursive.add(predicate_name)
    if cur_nonrecursive == extended_nonrecursive:
      return extended_nonrecursive
    else:
      return self.extend_nonrecursive_idb_predicate_names(extended_nonrecursive)
            
  
  def get_idb_predicate_names(self):
    idbs = set()
    for rule in self.get_derivation_rules():
      idbs.add(rule.head.name)
    return idbs 
  
  def get_edb_predicate_names(self):
    return self.get_predicate_names() - self.get_idb_predicate_names()
  
  def predicate_depends_on(self, predicate_name1, predicate_name2):
    return has_path(self.get_predicate_deps_graph(), predicate_name2, predicate_name1)
  
  def get_rules_for_predicate(self, predicate_name):
    rules = set()
    for rule in self.get_derivation_rules():
      if rule.head.name == predicate_name:
        rules.add(rule)
    return rules
  
  def get_predicate_deps_graph(self):
    if self.predicate_deps_graph != None:
      return self.predicate_deps_graph
    
    self.predicate_deps_graph = DiGraph()
    # add a node for each Predicate
    self.predicate_deps_graph.add_nodes_from(self.get_predicate_names())
    for predicate_name in self.get_predicate_names():
      for rule in self.get_rules_for_predicate(predicate_name):
        for literal in rule.get_literals():
          self.predicate_deps_graph.add_edge(literal.atom.name, predicate_name)
    return self.predicate_deps_graph
  
  def is_stratified(self):
    positivePredicateDeps = {}
    negativePredicateDeps = {}
    for predicate_name in self.get_predicate_names():
      positivePredicateDeps[predicate_name] = set()
      negativePredicateDeps[predicate_name] = set()
      for rule in self.get_rules_for_predicate(predicate_name):
        for literal in rule.get_literals():
          if literal.negated:
            negativePredicateDeps[predicate_name].add(literal.atom.name)
          else:
            positivePredicateDeps[predicate_name].add(literal.atom.name)
    for scc in strongly_connected_components(self.get_predicate_deps_graph()):
      for predicate_name in scc:
        if negativePredicateDeps[predicate_name].intersection(set(scc)):
          return False        
    return True
  
  def is_recursive_predicate(self, predicate_name):
    for cyclic_predicates in simple_cycles(self.get_predicate_deps_graph()):
      if predicate_name in cyclic_predicates:
        return True
    return False