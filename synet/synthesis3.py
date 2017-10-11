#!/usr/bin/env python

import argparse
import re
import z3
import networkx as nx
import itertools
from collections import Iterable
import os

#from translation.translator_nonrecursive import Translator
#from translation.translator_nonrecursive import get_string_const_val
#from translation import translator_nonrecursive as translator
from translation.translator import Translator
from translation.translator import get_string_const_val
from translation import translator

import tempfile

from common import *



__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"


# Get base dir to find the datalog models
BASEDIR = os.path.abspath(os.path.join(os.path.abspath(__file__), os.pardir))



# Define the boxes to load
BOXES = {}
BOXES['phy01'] = dict(file='%s/datalog/stratum-01-physical.logic' % BASEDIR)
BOXES['ospf01'] = dict(file='%s/datalog/stratum-02-ospf-01.logic' % BASEDIR)
BOXES['ospf02'] = dict(file='%s/datalog/stratum-03-ospf-02.logic' % BASEDIR)
BOXES['ospf02-0'] = dict(file='%s/datalog/stratum-03-ospf-02-0.logic' % BASEDIR)
BOXES['ospf02-1'] = dict(file='%s/datalog/stratum-03-ospf-02-1.logic' % BASEDIR)
BOXES['OSPF_FIXED'] = dict(file='%s/datalog/ospf-fixed.logic' % BASEDIR)
BOXES['ibgp01'] = dict(file='%s/datalog/stratum-04-ibgp-01.logic' % BASEDIR)
BOXES['ibgp02'] = dict(file='%s/datalog/stratum-05-ibgp-02.logic' % BASEDIR)
BOXES['ibgp03'] = dict(file='%s/datalog/stratum-06-ibgp-03.logic' % BASEDIR)
BOXES['ibgp04'] = dict(file='%s/datalog/stratum-07-ibgp-04.logic' % BASEDIR)
BOXES['ibgp05'] = dict(file='%s/datalog/stratum-08-ibgp-05.logic' % BASEDIR)
BOXES['ibgp06'] = dict(file='%s/datalog/stratum-09-ibgp-06.logic' % BASEDIR)
BOXES['ibgp07'] = dict(file='%s/datalog/stratum-10-ibgp-07.logic' % BASEDIR)
BOXES['ibgp08'] = dict(file='%s/datalog/stratum-11-ibgp-08.logic' % BASEDIR)
BOXES['ibgp09'] = dict(file='%s/datalog/stratum-12-ibgp-09.logic' % BASEDIR)
BOXES['fwd01'] = dict(file='%s/datalog/stratum-13-fwd-01.logic' % BASEDIR)
BOXES['fwd01-0'] = dict(file='%s/datalog/stratum-13-fwd-01-0.logic' % BASEDIR)
BOXES['fwd01-1'] = dict(file='%s/datalog/stratum-13-fwd-01-1.logic' % BASEDIR)
BOXES['fwd01-0-static'] = dict(file='%s/datalog/stratum-13-fwd-01-0-static.logic' % BASEDIR)
BOXES['fwd01-1-static'] = dict(file='%s/datalog/stratum-13-fwd-01-1-static.logic' % BASEDIR)

# Define the forward order for the box
boxes_order_all = [
    'phy01',
    'ospf01',
    'ospf02-0',
    'ospf02-1',
    'ibgp01',
    'ibgp02',
    'ibgp03',
    'ibgp04',
    'ibgp05',
    'ibgp06',
    'ibgp07',
    'ibgp08',
    'ibgp09',
    'fwd01-0',
    'fwd01-1',
    'fwd02',
    'fwd03',
]

boxes_order_simple = [
    'phy01',
    'ospf01',
    'fwd03',
]

BOXES_ORDER = ['ibgp01', 'ibgp02', 'ibgp03', 'ibgp04', 'ibgp05', 'ibgp06', 'ibgp07', 'ibgp08', 'ibgp09','ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']


# Define function signatures
# Need for input contraints and to query the model
FUNCS_SIG = {}
FUNCS_SIG['Vertex'] = ['String']
FUNCS_SIG['SetNode'] = ['Node']
FUNCS_SIG['SetInterface'] = ['Node', 'Interface']
FUNCS_SIG['SetNetwork'] = ['Node', 'Network']
FUNCS_SIG['Node'] = ['Node']
FUNCS_SIG['Interface'] = ['Interface']
FUNCS_SIG['Network'] = ['Network']
FUNCS_SIG['EdgePhy'] = ['Vertex', 'Vertex']
FUNCS_SIG['SetLink'] = ['Interface', 'Interface']
FUNCS_SIG['ConnectedNodes'] = ['Node', 'Interface', 'Interface', 'Node']

FUNCS_SIG['SetOSPFEdgeCost'] = ['Interface', 'Interface', 'Int']
FUNCS_SIG['LinkOSPF'] = ['Node', 'Node', 'Int']
FUNCS_SIG['OSPFRoute'] = ['Network', 'Node', 'Node', 'Int']
FUNCS_SIG['DJ'] = ['Node', 'Node', 'Node', 'Int']
FUNCS_SIG['OSPFRoute_unrolled'] = ['Network', 'Node', 'Node', 'Int']
FUNCS_SIG['nonMinOSPFRouteCost'] = ['Network', 'Node', 'Int']
FUNCS_SIG['minOSPFRouteCost'] = ['Network', 'Node', 'Int']
FUNCS_SIG['BestOSPFRoute'] = ['Network', 'Node', 'Node', 'Int']

FUNCS_SIG['SetBGPAnnouncement'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength']
FUNCS_SIG['BGPAnnouncement'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']
FUNCS_SIG['SetBGPLocalPref'] = ['Node', 'Network', 'AnnouncedNetwork', 'Int']
FUNCS_SIG['BGPRoute'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']
FUNCS_SIG['BGPLocalPref'] = ['Node', 'Network', 'AnnouncedNetwork', 'Int']
FUNCS_SIG['nonMaxBGPLocalPref'] = ['AnnouncedNetwork', 'Int']
FUNCS_SIG['MaxBGPLocalPrefBGPRoute'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']
FUNCS_SIG['ConnectedBGPAnnouncement'] = ['Node', 'Network', 'AnnouncedNetwork']
FUNCS_SIG['ConnectedBGPRoute'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']
FUNCS_SIG['nonMinAsPath'] = ['Node', 'AnnouncedNetwork', 'ASPathLength']

FUNCS_SIG['IGPRouteCost'] = ['Network', 'Node', 'Node', 'Int']
FUNCS_SIG['MinAsPathBGPRoute'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']

FUNCS_SIG['SetStaticRoute'] = ['Network', 'Node', 'Node']
FUNCS_SIG['SetStaticRouteCost'] = ['Network', 'Node', 'Node', 'Int']
FUNCS_SIG['StaticRouteCost'] = ['Network', 'Node', 'Node', 'Int']

FUNCS_SIG['IGPRouteCost'] = ['Network', 'Node', 'Node', 'Int']
FUNCS_SIG['nonMinIGPCost'] = ['Node', 'Network', 'Int']
FUNCS_SIG['MinIGPBGPRoute'] = ['Node', 'Network', 'AnnouncedNetwork', 'ASPath', 'ASPathLength', 'Int']


FUNCS_SIG['Route'] = ['NetworkOrAnnouncedNetwork', 'Node', 'Node', 'Protocol']
FUNCS_SIG['BestBGPRoute'] = ['AnnouncedNetwork', 'Node', 'Node']
FUNCS_SIG['Fwd'] = ['NetworkOrAnnouncedNetwork', 'Node', 'Node', 'Protocol']
FUNCS_SIG['SetAdminDist'] = ['Node', 'Protocol', 'Int']
FUNCS_SIG['nonMinCostAD'] = ['NetworkOrAnnouncedNetwork', 'Node', 'Int']
FUNCS_SIG['OutgoingFwdInterface'] = ['NetworkOrAnnouncedNetwork', 'Node', 'Interface']
FUNCS_SIG['IncomingFwdInterface'] = ['NetworkOrAnnouncedNetwork', 'Interface', 'Node']
FUNCS_SIG['ConnectedDirectly'] = ['Vertex', 'Node']
FUNCS_SIG['EdgePhy'] = ['Vertex', 'Vertex']
FUNCS_SIG['EdgeFwd'] = ['NetworkOrAnnouncedNetwork', 'Vertex', 'Vertex']
FUNCS_SIG['ReachFwd'] = ['NetworkOrAnnouncedNetwork', 'Vertex', 'Vertex', 'Protocol']
FUNCS_SIG['ReachFwd_unrolled'] = ['NetworkOrAnnouncedNetwork', 'Vertex', 'Vertex']


def parse_inputs(inputs):
    """
    Parse logicblox input of the form +Name(args,...) and returns
    a list of tuples such as (Name, (args)).
    """
    p = re.compile(r'^(?P<op>[\+|\-])(?P<name>\w[\w\d_]*)\((?P<args>.*)\)\.$')
    init_inputs = []
    for line in inputs.split("\n"):
        line = line.strip()
        if not line: continue
        if not re.match(p, line):
            if line.startswith("//"):
                continue
            print "Not valid input, skipping", line
            continue
        m = re.match(p, line)
        op = m.group('op')
        func_name = m.group('name')
        args = m.group('args').replace(' ', '').replace('"', '').split(',')
        init_inputs.append((op, func_name, args))
    return init_inputs


# Keep track of the highest unrolled version of each function
# If the function is not unrolled, then it will map back to itself
UNROLLED = {}

# Keep track of the original function name for each function (unrolled or not)
# If the function is not unrolled, then it will map back to itself
MAP_TO_ORIGINAL = {}


def get_unrolled_version(name):
    return UNROLLED.get(get_original_version(name), name)


def get_original_version(name):
    return MAP_TO_ORIGINAL[name]


def fill_box_info(box_name, unrolling_limit):
    print "IN BOX", box_name
    box = Translator(BOXES[box_name]['file'], unrolling_limit)
    BOXES[box_name]['box'] = box
    BOXES[box_name]['constraints'] = box.to_z3()
    BOXES[box_name]['solver'] = z3.Solver()
    BOXES[box_name]['solver'].set(unsat_core=True)
    BOXES[box_name]['inputs'] = {}
    BOXES[box_name]['outputs'] = {}
    BOXES[box_name]['fixed_inputs'] = []
    BOXES[box_name]['fixed_outputs'] = []
    BOXES[box_name]['input_constraints'] = []
    for name in box.program.get_edb_predicate_names():
        func = box.predicates[name]
        BOXES[box_name]['inputs'][name] = func
        assert name in FUNCS_SIG, name
        assert len(FUNCS_SIG[name]) == func.arity(), func
        if name not in UNROLLED:
            UNROLLED[name] = name
        MAP_TO_ORIGINAL[name] = name
    for name in box.program.get_idb_predicate_names():
        func = box.predicates[name]
        BOXES[box_name]['outputs'][str(func)] = func
        assert str(func) in FUNCS_SIG, str(func)
        assert len(FUNCS_SIG[str(func)]) == func.arity(), "%s, %s, %s" % (str(func), [func.domain(i) for i in range(func.arity())],  FUNCS_SIG[str(func)])
        MAP_TO_ORIGINAL[name] = name
        for i in range(1, box.unroll_limit + 1):
            func = box.get_predicate(name, i)
            BOXES[box_name]['outputs'][str(func)] = func
            assert str(name) in FUNCS_SIG, name
            assert len(FUNCS_SIG[name]) == func.arity(), str(func)
            FUNCS_SIG[str(func)] = FUNCS_SIG[name]
            MAP_TO_ORIGINAL[str(func)] = name
            if i == box.unroll_limit:
                UNROLLED[name] = str(func)


class Synthesizer(object):
    def __init__(self, boxes_names, inputs, fixed_outputs, unrolling_limit=5):
        self.boxes_names = boxes_names
        self.init_inputs = []
        self.node_interface = []
        self.node_network = []
        self.links = []
        self.protocols = []
        self.as_paths = []
        self.fixed_inputs = {}
        self.parse_initial_inputs(inputs)
        self.set_bgp_annoucement = {}
        self._create_vertices('Vertex')
        self.network_graph = nx.DiGraph()
        self.unrolling_limit = unrolling_limit
        self.ospf_costs = {}
        self.static_routes = {}

        for box_name in self.boxes_names:
            fill_box_info(box_name, unrolling_limit)

        self.read_init_inputs()
        self.read_fixed_outputs(fixed_outputs)
        self.construct_input_graph()
        #draw(self.network_graph, '/tmp/gg.ddot')
        self._fill_boxes()
        self.build_dependency_graph()

    def build_dependency_graph(self):
        self.dep_g = nx.DiGraph()
        for box_name in self.boxes_names:
            self.dep_g.add_node(box_name)
        for src in self.boxes_names:
            for dst in self.boxes_names:
                src_set = set(BOXES[src]['outputs'].keys())
                dst_set = set(BOXES[dst]['inputs'].keys())
                if src_set.intersection(dst_set):
                    self.dep_g.add_edge(src, dst)
        #nx_pydot.write_dot(self.dep_g, '/tmp/ddep.ddot')

    def _fill_boxes(self):
        """
        Fill input, output constraints and load them to the solver of
        each box.
        """
        for box_name in self.boxes_names:
            self.fill_boxes_input_constraints(box_name)
            # Load input constraints
            BOXES[box_name]['solver'].append(BOXES[box_name]['box'].to_z3())
            for c in BOXES[box_name]['input_constraints']:
                if c is None: continue
                #print "Added constrains", box_name, c
                BOXES[box_name]['solver'].append(c)
            # Load fixed input by the user

            print "Loading user provided input for box:", box_name, BOXES[box_name]['fixed_inputs']
            BOXES[box_name]['solver'].append(BOXES[box_name]['fixed_inputs'])
            print "Checking initial inputs for box", box_name
            #assert BOXES[box_name]['solver'].check() == z3.sat, \
            #    "%s: %s" % (box_name, BOXES[box_name]['box'].to_z3())
            print "Loading user provided outputs for box:", box_name, BOXES[box_name]['fixed_outputs']
            for i in BOXES[box_name]['inputs']:
                if i in self.fixed_inputs:
                    #print "TO APPEND", box_name, self.fixed_inputs[i]
                    BOXES[box_name]['solver'].append(self.fixed_inputs[i])
            BOXES[box_name]['solver'].append(BOXES[box_name]['fixed_outputs'])
            #if box_name == 'fwd03':
            #    fwd = BOXES[box_name]['inputs']['Fwd']
            #    BOXES[box_name]['solver'].append(fwd(get_string_const_val('N1')))
        print ''

    def evaluate_function(self, func, model):
        func_name = str(func)
        values = []
        def get_domain_values(domain):
            if domain == 'Vertex':
                return self.all_vertices
            elif domain == 'Node':
                return self.nodes
            elif domain == 'Network':
                return self.networks
            elif domain == 'Interface':
                return self.interfaces
            elif domain == 'AnnouncedNetwork':
                return self.announced_networks
            elif domain == 'NetworkOrAnnouncedNetwork':
                return self.announced_networks + self.networks
            elif domain == 'Protocol':
                return [get_string_const_val(p) for p in ['static', 'ospf', 'bgp']]
            elif domain == 'ASPath':
                return [get_string_const_val(p) for p in self.as_paths]
            elif domain == 'Int':
                return list(range(100))
            else:
                raise ValueError("Unknown domain '%s" % domain)
        domains = [get_domain_values(arg) for arg in FUNCS_SIG[func_name]]
        for vals in itertools.product(*domains):
            values.append((vals, z3.is_true(model.eval(func(*vals), True))))
        return values

    def _process_vals(self, func, vals, functions, return_else=True):
        #print "-" * 30
        #print "IN PROCESS VALS", func, vals
        #return_else = False
        func_name = str(func)
        variables = []
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']
        for i, t in enumerate(FUNCS_SIG[func_name]):
            if t == 'Vertex':
                variables.append(z3.Const('t%d' % i, self.vertex))
            elif t == 'Node':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
            elif t == 'Network':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
            elif t == 'Interface':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
            elif t == 'AnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
            elif t == 'NetworkOrAnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
            elif t == 'Int':
                variables.append(z3.Const('t%d' % i, z3.IntSort()))
            elif t == 'ASPath':
                tmp = z3.Const('t%d' % i, string_sort)
                variables.append(tmp)
            elif t == 'ASPathLength':
                variables.append(z3.Const('t%d' % i, z3.IntSort()))
            elif t == 'Protocol':
                tmp = z3.Const('t%d' % i, string_sort)
                variables.append(tmp)
            else:
                raise ValueError(
                    "Unrecoginzed function %s domain '%s" % (func_name, t))

        global_ret = None
        for val in vals[:]:
            if str(val) in ['True', 'False']:
                vals.remove(val)
                ret = True if val == 'True' else False
                global_ret = ret

        true_set = [val for val in vals if z3.is_expr(val[-1]) and z3.is_true(val[-1])]
        false_set = [val for val in vals if z3.is_expr(val[-1]) and z3.is_false(val[-1])]

        c = []
        if true_set:
            for val in true_set:
                f_name = get_unrolled_version(func_name)
                f = functions.get(f_name, func)
                c.append(f(*val[:-1]) == True)
        if false_set:
            f_name = get_original_version(func_name)
            f = functions[f_name]
            for val in false_set:
                c.append(f(*val[:-1]) == False)

        if global_ret is not None:
            if global_ret == True:
                f_name = get_unrolled_version(func_name)
                f = functions.get(f_name, func)
            else:
                f_name = get_original_version(func_name)
                f = functions[f_name]
            if len(vals) > 0:
                if return_else:
                    c.append(
                        z3.ForAll(
                            variables,
                            z3.Implies(
                                z3.Not(z3.Or([z3.And(
                                    [v == val[i] for i, v in enumerate(variables)])
                                              for
                                              val in vals])),
                                f(*variables) == global_ret)))
            else:
                c.append(z3.ForAll(variables, f(*variables) == global_ret))
        #print "Final constrinats", c
        #print "-" * 30
        return c

    def _get_function_vals(self, func, model):
        """Recursively go through the model to get the values of a function"""
        vals = []
        if model[func] is None:
            return vals
        if str(func) in ['True', 'False']:
            vals.append(str(func))
            return vals
        for val in model[func].as_list()[:-1]:
            vals.append(val)
        el = model[func].else_value()
        if z3.is_true(el) or z3.is_false(el):
            vals.append(str(el))
            return vals
        ret = self._get_function_vals(el.decl(), model)
        if ret:
            vals.extend(ret)
        return vals

    def print_box_results(self, box_name):
        print "For box", box_name
        model = BOXES[box_name]['solver'].model()
        for name, func in BOXES[box_name]['inputs'].iteritems():
            vals = self._get_function_vals(func, model)
            filterd_val = [val[:-1] if z3.is_expr(val[-1]) else val for val in
                           vals]
            print "\tSynthesized input", name, filterd_val
            if name == 'SetOSPFEdgeCost':
                for val in filterd_val:
                    if isinstance(val, basestring): continue
                    self.ospf_costs[(self.get_name(val[0]), self.get_name(val[1]))] = val[2]
            if name == 'SetStaticRoute':
                for val in filterd_val:
                    if isinstance(val, basestring): continue
                    net = self.get_name(val[0])
                    src = self.get_name(val[1])
                    dst = self.get_name(val[2])
                    if src not in self.static_routes:
                        self.static_routes[src] = []
                    self.static_routes[src].append((net, src, dst))
        for name, func in BOXES[box_name]['outputs'].iteritems():
            vals = self._get_function_vals(func, model)
            filterd_val = [val[:-1] for val in vals if z3.is_true(val[-1])]
            print "\tSynthesized output", name, filterd_val

    def get_dj_constraints(self, dj, vals):
        ret = []
        t1, t2 = z3.Consts('t1 t2', z3.IntSort())
        v1, v2 = z3.Consts('v1 v2', self.vertex)

        net_map = {}
        for src, net in self.connected_networks:
            net_map[net] = src

        considered = []
        for val in vals:
            print "In val", val
            if not isinstance(val, list):
                continue
            net, src, nxt = val[0], val[1], val[2]
            r = self.get_vertex(net_map[str(net)])
            ss = [str(r), str(src), str(nxt)]
            if ss not in considered:
                considered.append(ss)
            else:
                continue
            c = z3.And(
                z3.Exists([t1], dj(r, src, nxt, t1)),
                z3.Not(z3.Exists([v1, t2], z3.And(
                    dj(r, src, v1, t2),
                    v1 != v2,
                    t2 < t1
                ))
                       ))
            print "Added", c
            ret.append(c)
        return ret

    def get_ospf_constraints(self, ospf_route, ospf_route2, vals):
        ret = []
        t1, t2 = z3.Consts('t1 t2', z3.IntSort())
        v1, v2 = z3.Consts('v1 v2', self.vertex)

        for val in vals:
            if not isinstance(val, list):
                continue
            net, src, nxt = val[0], val[1], val[2]
            c = z3.And(
                z3.Exists([t1], ospf_route(net, src, nxt , t1)),
                z3.Not(z3.Exists([v1, t2], z3.And(
                    ospf_route2(net, src, v1, t2),
                    v1 != v2,
                    t2 < t1
                ))
            ))
            ret.append(c)
        return ret

    def synthesize(self):
        print "Beginning Synthesis..."
        yes_func_vals = {}
        no_box_vals = dict([(box_name, []) for box_name in self.boxes_names])
        box_index = len(self.boxes_names) - 1
        box_tries_count = dict([(box_name, 0) for box_name in self.boxes_names])
        while True:
            box_name = self.boxes_names[box_index]
            box_tries_count[box_name] += 1
            if box_name == 'OSPF_FIXED':
                print "Using custom OSPF " * 5
                ff = []
                for val in yes_func_vals['BestOSPFRoute']:
                    if val == 'False':
                        continue
                    elif val == 'True':
                        raise ValueError("All values must be explicitly specificed for OSPFRoute")
                    else:
                        ff.append(OSPFSyn.BestOSPFRoute(*[str(v) for v in val[:-1]]))
                ospf_syn = OSPFSyn(ff, self.network_graph)
                BOXES[box_name]['ospf_fixed'] = ospf_syn
                assert ospf_syn.solve()
                costs = []
                for out in ospf_syn.get_output_configs():
                    if not isinstance(out, OSPFSyn.SetOSPFEdgeCost): continue
                    c = [self.get_vertex(out.src),
                         self.get_vertex(out.dst),
                         int(out.cost), z3.BoolVal(True)]
                    costs.append(c)
                costs.append(z3.BoolVal(False))
                yes_func_vals['SetOSPFEdgeCost'] = costs
                box_index -= 1
                if box_index < 0:
                    print "Done!!!"
                    break
                else:
                    continue
            if box_name == 'ospf01':
              solver = z3.Solver()
              print 'partially evaluate the OSPF Datalog rules'
              translator = Translator(BOXES[box_name]['file'], 1)
              ospf_costs = {}
              DEBUG_OSPF = False
              if DEBUG_OSPF:                
                ospf_routes = []
                for ospf_route in BOXES[box_name]['fixed_outputs']:
                  ospf_route = ospf_route.arg(0)
                  net = ospf_route.arg(0)
                  src = ospf_route.arg(1)
                  nxt = ospf_route.arg(2)
                  cost = ospf_route.arg(3)
                  ospf_routes.append([net, src, nxt, cost])
                yes_func_vals['OSPFRoute'] = ospf_routes                          
              for out in yes_func_vals['OSPFRoute']:
                if str(out) == 'False' :
                  continue
                net = str(out[0])
                if net not in ospf_costs.keys():
                  ospf_costs[net] = {}
                src = str(out[1])
                if src not in ospf_costs[net].keys():
                  ospf_costs[net][src] = {}
                nxt = str(out[2])                
                cost = str(out[3])
                ospf_costs[net][src][nxt] = cost
              ospf_reduced = tempfile.NamedTemporaryFile() #open('/tmp/ospf_reduced.sssmt2', 'w')
              print 'Writing OSPF partial evaluation rules to:', ospf_reduced.name
              ospf_reduced.write("""// ----------------------------- TYPES ----------------------------- //
                                  // Generic Vertex type
                                  Vertex(n) -> string(n).
                                  ConnectedNodes(snode, siface, diface, dnode) ->
                                  Vertex(snode), Vertex(siface), Vertex(diface), Vertex(dnode).
                                  //EDB: SetOSPFEdgeCost, Node, Network, EdgePhy
                                  SetOSPFEdgeCost(src, dst, cost) -> Vertex(src), Vertex(dst), int(cost).                                  
                                  //IDB: LinkOSPF, OSPFRoute
                                  OSPFRoute(net, src, next, cost) -> Vertex(net), Vertex(src), Vertex(next), int(cost).
                                  
                                  // ----------------------------- OSPF 1/2 ----------------------------- //
                                  """)
              for rule in translator.program.get_rules_for_predicate('OSPFRoute'):
                if rule.head.name in [l.atom.name for l in rule.get_literals()]:
                  print rule
                  for net in ospf_costs.keys():
                    for src in ospf_costs[net].keys():
                      for nxt in ospf_costs[net][src].keys():
                        src_nxt_link = [link for link in self.connected_nodes if link[0] == src and link[3] == nxt][0]
                        src_iface = src_nxt_link[1] 
                        nxt_iface = src_nxt_link[2]
                        if nxt not in ospf_costs[net].keys():                          
                          newRule = 'OSPFRoute_{}_{}_{}(cost) <- SetOSPFEdgeCost(src, nxt, cost  ), src="{}", nxt="{}", cost = {}.'.format(net, src, nxt, src_iface, nxt_iface, ospf_costs[net][src][nxt])
                          print newRule
                          ospf_reduced.write(newRule + '\n')
                          newRule = 'OSPFRoute_{}_{}_{}(cost) -> int(cost).'.format(net, src, nxt)
                          print newRule
                          ospf_reduced.write(newRule + '\n')
                        else:
                          for next2 in ospf_costs[net][nxt].keys():                            
                            newRule = 'OSPFRoute_{}_{}_{}(cost) <- SetOSPFEdgeCost(src, nxt, cost1), src="{}", nxt="{}", cost = cost1 + {}.'.format(net, src, nxt, src_iface, nxt_iface, ospf_costs[net][nxt][next2])
                            print newRule
                            ospf_reduced.write(newRule + '\n')
                            newRule = 'OSPFRoute_{}_{}_{}(cost) -> int(cost).'.format(net, src, nxt)
                            print newRule
                            ospf_reduced.write(newRule + '\n')
              
              ospf_reduced.flush()
              newTranslator = Translator(ospf_reduced.name, self.unrolling_limit)
              newTranslator.STRING_TO_VERTEX = self.name_to_vertex
              BOXES[box_name]['solver'] = z3.Solver()            
              BOXES[box_name]['solver'].append(newTranslator.to_z3())
                          
              for fix_output in yes_func_vals['OSPFRoute']:                
                if str(fix_output) == 'False':
                  continue
                net = fix_output[0] 
                src = fix_output[1]
                nxt = fix_output[2]
                cost = fix_output[3]
                c = newTranslator.predicates['OSPFRoute_{}_{}_{}'.format(net, src, nxt)](cost) == True
                print c
                BOXES[box_name]['solver'].append(c)
                t = z3.Const('cost', z3.IntSort())
                c = z3.ForAll([t], newTranslator.predicates['OSPFRoute_{}_{}_{}'.format(net, src, nxt)](t) == (t == cost))
                print c
                BOXES[box_name]['solver'].append(c)
              
              for c in BOXES[box_name]['input_constraints']:
                  if c is None: continue
                  c
                  BOXES[box_name]['solver'].append(c)
              BOXES[box_name]['solver'].append(BOXES[box_name]['fixed_inputs'])
              for i in BOXES[box_name]['inputs']:
                  if i in self.fixed_inputs:
                      #print "TO APPEND", box_name, self.fixed_inputs[i]
                      BOXES[box_name]['solver'].append(self.fixed_inputs[i])
              BOXES[box_name]['solver'].append(BOXES[box_name]['fixed_outputs'])
              
            solver = BOXES[box_name]['solver']
            solver.push()
            print "#" * 30
            print "Synthesizing for box", box_index, box_name
            print "Feeding desired outputs for %s..." % box_name
            # Generate custom constraints for aggregation in min
            '''
            if box_name in ['ospf01']:
                orig_name = get_original_version('BestOSPFRoute')
                vals = yes_func_vals[orig_name]
                c = self.get_ospf_constraints(
                    BOXES[box_name]['outputs']['OSPFRoute_%d' % self.unrolling_limit],
                    BOXES[box_name]['outputs']['OSPFRoute'], vals)
                solver.append(c)
            '''
            if box_name in ['opt2']:
                orig_name = get_original_version('BestOSPFRoute')
                vals = yes_func_vals[orig_name]
                c = self.get_dj_constraints(BOXES[box_name]['outputs']['DJ'],
                                              vals)
                solver.append(c)
            for func_name, func in BOXES[box_name]['outputs'].iteritems():
                # Pre compute IGPRouteCost of OSPF
                if func_name == 'MinIGPBGPRoute' and 'BestOSPFRoute' in yes_func_vals and 'IGPRouteCost' in BOXES[box_name]['inputs']:
                    IGPRouteCost = BOXES[box_name]['inputs']['IGPRouteCost']
                    valid_igp = []
                    for bestOSPF in yes_func_vals['BestOSPFRoute']:
                        if str(bestOSPF[-1]) == 'True':
                            valid_igp.append(bestOSPF)
                    if 'SetStaticRoute' in yes_func_vals:
                        static = yes_func_vals['SetStaticRoute']
                        for v in static:
                            if str(v[-1]) != 'True': continue
                            print "Added static", v
                            #valid_igp.append(v + [1])

                    print "Synthesized IGPRouteCost", [(p[0], p[1], p[2], p[3]) for p in valid_igp]

                    v1, v2, v3 = z3.Consts('v1 v2 v3', self.vertex)
                    t1 = z3.Const('t1', z3.IntSort())
                    c = z3.ForAll(
                        [v1, v2, v3, t1],
                            IGPRouteCost(v1, v2, v3, t1) ==
                                z3.Or(
                                    *[z3.And(v1 == p[0], v2 == p[1], v3 == p[2], t1 == p[3]) for p in valid_igp]
                                ),


                    )

                    solver.append(c)
                orig_name = get_original_version(func_name)
                return_else = True
                if orig_name in ['BGPLocalPref', 'OSPFRoute']:
                    return_else = False
                if orig_name in yes_func_vals:
                    fed_output = self._process_vals(
                        func,
                        yes_func_vals[orig_name],
                        BOXES[box_name]['outputs'],
                        return_else=return_else)
                    print "\tFeeding desired output", box_name, fed_output
                    #print fed_output
                    solver.append(fed_output)
            for t in no_box_vals[box_name]:
                #print "\tFeeding NOT desired input", box_name, t
                pass
            # Short cut inputs
            for func_name, func in BOXES[box_name]['inputs'].iteritems():
                orig_name = get_original_version(func_name)
                return_else = True
                if orig_name in ['BGPLocalPref', 'OSPFRoute', 'nonMinOSPFRouteCost', 'nonMaxBGPLocalPref']:
                    return_else = False
                if orig_name in yes_func_vals:
                    fed_output = self._process_vals(
                        func,
                        yes_func_vals[orig_name],
                        BOXES[box_name]['inputs'],
                        return_else=return_else)
                    print "\tFeeding shortcut INPUT", box_name, fed_output
                    solver.append(fed_output)
            solver.append(no_box_vals[box_name])
            print "Checking SAT for box %s ..." % box_name
            #smt2_dump = open('last.smt2', 'w')
            #smt2_dump.write(solver.to_smt2())
            #smt2_dump.close()
            #print solver.to_smt2()
            if solver.check() == z3.sat:
                box_tries_count[box_name] = 1
                print 'SAT, reading inputs...'
                model = solver.model()
                for name, func in BOXES[box_name]['inputs'].iteritems():
                    if name == 'BGPRoute': continue
                    vals = self._get_function_vals(func, model)
                    if len(vals) == 0:
                        vals = ['False']
                    #else:
                    #    vals.append('False')
                    yes_func_vals[name] = vals
                    print "\tSynthesized input", name, vals
                box_index -= 1
                if box_index < 0:
                    print "Done!!!"
                    break
                #return
            else:
                #print "FAILED!!!"
                #print BOXES[box_name]['box'].to_z3()
                #print solver.to_smt2()
                #if box_index < len(self.boxes_names) - 1:
                #    self.print_box_results(self.boxes_names[box_index + 1])
                #return
                if box_index == len(self.boxes_names) - 1:
                    print "FAILED!!!"
                    return
                solver.pop()
                box_index += 1
                #box_index = len(self.boxes_names) - 1
                #box_index = len(self.boxes_names) - 1
                box_name = self.boxes_names[box_index]
                print "!" * 20
                print "UNSAT going back to", box_index, box_name
                no_vals = []
                for func_name, func in BOXES[box_name]['inputs'].iteritems():
                    orig_name = get_original_version(func_name)
                    if orig_name not in yes_func_vals:
                        continue
                    vals = yes_func_vals[orig_name]
                    if len(vals) == 0:
                        vals = ['False']
                    else:
                        vals.append('False')
                    vals = self._process_vals(func, vals, BOXES[box_name]['inputs'], return_else=True)
                    no_vals.extend(vals)
                    del yes_func_vals[func_name]
                if box_name not in no_box_vals:
                    no_box_vals[box_name] = []
                no_box_vals[box_name].append(z3.Not(z3.And(*no_vals)))
        #for box_name in self.boxes_names:
        #    print BOXES[box_name]['solver'].model()
        print "$"*40
        print "Final results..."
        for box_name in self.boxes_names:
            if box_name == 'OSPF_FIXED':
                print "For box", box_name
                syn = BOXES['OSPF_FIXED']['ospf_fixed']
                for out in syn.get_output_configs():
                    print "\t", out
            else:
                self.print_box_results(box_name)

    def _common_datatypes(self):
        """Common dataypes Node, Networks, Interfaces"""
        # Common
        is_node = z3.Function('is_node', self.vertex, z3.BoolSort())
        is_network = z3.Function('is_network', self.vertex, z3.BoolSort())
        is_interface = z3.Function('is_interface', self.vertex, z3.BoolSort())
        is_announced_network = z3.Function('is_announced_network', self.vertex, z3.BoolSort())
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']
        is_protocol = z3.Function('is_protocol', string_sort, z3.BoolSort())
        is_as_path = z3.Function('is_as_path', string_sort, z3.BoolSort())
        is_as_path_length = z3.Function('is_as_path_length', string_sort, z3.IntSort(), z3.BoolSort())
        protocols = [get_string_const_val('static'),
                     get_string_const_val('ospf'),
                     get_string_const_val('bgp')]
        as_paths = [get_string_const_val(p) for p in self.as_paths]
        v1 = z3.Const('v1', self.vertex)
        s1 = z3.Const('s1', string_sort)
        t1 = z3.Const('t1', z3.IntSort())
        self.connected_networks_f = z3.Function('ConnectedNetwork', self.vertex, self.vertex, z3.BoolSort())

        constraints = []
        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.Or([v1 == tmp for tmp in self.nodes]),
                    is_node(v1) == True
                )))
        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.And([v1 != tmp for tmp in self.nodes]),
                    is_node(v1) == False
                )))
        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.Or([v1 == tmp for tmp in self.networks]),
                    is_network(v1) == True
                )))
        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.And([v1 != tmp for tmp in self.networks]),
                    is_network(v1) == False
                )))

        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.Or([v1 == tmp for tmp in self.interfaces]),
                    is_interface(v1) == True
                )))
        constraints.append(
            z3.ForAll(
                [v1],
                z3.Implies(
                    z3.And([v1 != tmp for tmp in self.interfaces]),
                    is_interface(v1) == False
                )))
        if self.announced_networks:
            constraints.append(
                z3.ForAll(
                    [v1],
                    z3.Implies(
                        z3.Or([v1 == tmp for tmp in self.announced_networks]),
                        is_announced_network(v1) == True
                    )))
            constraints.append(
                z3.ForAll(
                    [v1],
                    z3.Implies(
                        z3.And([v1 != tmp for tmp in self.announced_networks]),
                        is_announced_network(v1) == False
                    )))
        else:
            constraints.append(z3.ForAll([v1], is_announced_network(v1) == False))

        constraints.append(
            z3.ForAll(
                [s1],
                z3.Implies(
                    z3.Or([s1 == tmp for tmp in protocols]),
                    is_protocol(s1) == True
                )))
        constraints.append(
            z3.ForAll(
                [s1],
                z3.Implies(
                    z3.And(
                        [s1 != tmp for tmp in protocols]),
                    is_protocol(s1) == False
                )))

        if as_paths:
            constraints.append(
                z3.ForAll(
                    [s1],
                    z3.Implies(
                        z3.Or([s1 == tmp for tmp in as_paths]),
                        is_as_path(s1) == True
                    )))
            constraints.append(
                z3.ForAll(
                    [s1],
                    z3.Implies(
                        z3.And(
                            [s1 != tmp for tmp in as_paths]),
                        is_as_path(s1) == False
                    )))
        else:
            constraints.append(z3.ForAll([s1],  is_as_path(s1) == False))

        if self.as_paths_length:
            constraints.append(
                z3.ForAll(
                    [s1, t1],
                    z3.Implies(
                        z3.Or(
                            [z3.And(s1 == p, t1 == l) for p, l in self.as_paths_length.iteritems()]),
                        is_as_path_length(s1, t1) == True
                    )))
            constraints.append(
                z3.ForAll(
                    [s1],
                    z3.Implies(
                        z3.And(
                                [z3.Not(z3.And(s1 == p, t1 == l))
                                 for p, l in self.as_paths_length.iteritems()]),
                        is_as_path_length(s1, t1) == False
                    )))
        else:
            constraints.append(
                z3.ForAll([s1, t1], is_as_path_length(s1, t1) == False))
        # Pair of directly connected routers
        self.directly_connected_nodes = z3.Function('DirectlyConnectedNodes',
                                                    self.vertex, self.vertex,
                                                    z3.BoolSort())


        return is_node, is_network, is_interface, is_announced_network, is_protocol, is_as_path, is_as_path_length, constraints

    def is_connected_to_same(self, net1, net2):
        r1, r2 = None, None
        for r, net in self.connected_networks:
            if net == net1:
                r1 = r
            elif net == net2:
                r2 = r
            if r1 and r2:
                break
        return r1 == r2

    def fill_connected_networks_f(self):
        if not hasattr(self, '_tmp_connected_networks'):
            self._tmp_connected_networks = []
        if self._tmp_connected_networks:
            return self._tmp_connected_networks
        constraints = []
        for src in self.all_vertices:
            for dst in self.all_vertices:
                if (str(src), str(dst)) in self.connected_networks:
                    constraints.append(self.connected_networks_f(src, dst) == True)
                else:
                    constraints.append(
                        self.connected_networks_f(src, dst) == False)
        self._tmp_connected_networks = constraints
        return self._tmp_connected_networks

    def fill_directly_connected_nodes(self):
        if not hasattr(self, '_tmp_dnodes'):
            self._tmp_dnodes = []
        if self._tmp_dnodes:
            return self._tmp_dnodes
        constraints = []
        direct_nodes = []
        for snode in self.node_names:
            for siface in self.interface_names:
                for diface in self.interface_names:
                    for dnode in self.node_names:
                        l = [snode, siface, diface, dnode]
                        if l in self.connected_nodes:
                            direct_nodes.append((snode, dnode))
        direct_nodes = list(set(direct_nodes))
        for snode in self.node_names:
            for dnode in self.node_names:
                sv = self.get_vertex(snode)
                dv = self.get_vertex(dnode)
                if (snode, dnode) in direct_nodes:
                    constraints.append(
                        self.directly_connected_nodes(sv, dv) == True)
                else:
                    constraints.append(
                        self.directly_connected_nodes(sv, dv) == False)
        self._tmp_dnodes = constraints
        return self._tmp_dnodes

    def generate_function_constraints(self, func):
        is_node, is_network, is_interface, is_announced_network, is_protocol, is_as_path, is_as_path_length, constraints = self._common_datatypes()
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']
        func_name = str(func)
        assert func_name in FUNCS_SIG, \
            "The function '%s' has no signature defined" % func_name
        assert len(FUNCS_SIG[func_name]) == func.arity(), \
            "The function '%s' has different signature" % func_name
        variables = []
        checks = []
        for i, t in enumerate(FUNCS_SIG[func_name]):
            if t == 'Vertex':
                variables.append(z3.Const('t%d' % i, self.vertex))
            elif t == 'Node':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
                checks.append(z3.Not(is_node(tmp)))
            elif t == 'Network':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
                checks.append(z3.Not(is_network(tmp)))
            elif t == 'Interface':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
                checks.append(z3.Not(is_interface(tmp)))
            elif t == 'AnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
                checks.append(z3.Not(is_announced_network(tmp)))
            elif t == 'NetworkOrAnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.vertex)
                variables.append(tmp)
                checks.append(z3.Not(z3.Or(is_announced_network(tmp), is_network(tmp))))
            elif t == 'Int':
                tmp = z3.Const('t%d' % i, z3.IntSort())
                variables.append(tmp)
                if func_name.startswith('OSPFRoute'):
                    checks.append(z3.Not(z3.And(tmp <= 30, tmp >= 0)))
                else:
                    checks.append(z3.Not(z3.And(tmp <= 17, tmp >= 0)))
            elif t == 'ASPathLength':
                tmp = z3.Const('t%d' % i, z3.IntSort())
                variables.append(tmp)
                if FUNCS_SIG[func_name][i - 1] == 'ASPath':
                    p = variables[-2]
                    checks.append(z3.Not(is_as_path_length(p, tmp)))
            elif t == 'ASPath':
                tmp = z3.Const('t%d' % i, string_sort)
                variables.append(tmp)
                checks.append(z3.Not(is_as_path(tmp)))
            elif t == 'Protocol':
                tmp = z3.Const('t%d' % i, string_sort)
                variables.append(tmp)
                checks.append(z3.Not(is_protocol(tmp)))
            else:
                raise ValueError("Unrecoginzed function %s domain '%s" % (func_name, t))

        c = [z3.ForAll(variables, z3.Not(z3.And(func(*variables), z3.Or(*checks))))]
        if func_name == 'BGPAnnouncement':
            c.append(
                z3.ForAll(
                    variables,
                    z3.Implies(
                        z3.Not(
                            z3.Or([z3.And([v == announcement[i] for i, v in enumerate(variables)]) for announcement in self.bgp_annoucements])),
                        z3.Not(func(*variables)))))
        return c

    def fill_boxes_input_constraints(self, box_name):
        #if box_name == 'ospf01':
        #  return
        inputs = BOXES[box_name]['inputs']
        outputs = BOXES[box_name]['outputs']
        is_node, is_network, is_interface, is_announced_network, is_protocol, is_as_path, is_as_path_length, constraints = self._common_datatypes()
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']

        Node = inputs.get('Node', None)
        Interface = inputs.get('Interface', None)
        Network = inputs.get('Network', None)
        EdgePhy = inputs.get('EdgePhy', outputs.get('EdgePhy', None))
        SetNetwork = inputs.get('SetNetwork', None)
        SetInterface = inputs.get('SetInterface', None)
        SetLink = inputs.get('SetLink', outputs.get('SetLink', None))
        LinkOSPF = inputs.get('LinkOSPF', outputs.get('LinkOSPF', None))
        SetOSPFEdgeCost = inputs.get('SetOSPFEdgeCost', outputs.get('SetOSPFEdgeCost', None))
        StaticRouteCost = inputs.get('StaticRouteCost', None)
        IGPRouteCost = inputs.get('IGPRouteCost', outputs.get('IGPRouteCost', None))
        ConnectedBGPRoute = inputs.get('ConnectedBGPRoute', outputs.get('ConnectedBGPRoute', None))
        BestOSPFRoute = inputs.get('BestOSPFRoute', outputs.get('BestOSPFRoute', None))
        OSPFRoute = inputs.get('OSPFRoute', outputs.get('OSPFRoute', None))
        nonMinOSPFRouteCost = inputs.get('nonMinOSPFRouteCost', outputs.get('nonMinOSPFRouteCost', None))
        Route = inputs.get('Route', outputs.get('Route', None))
        SetStaticRouteCost = inputs.get('SetStaticRouteCost', None)
        SetStaticRoute = inputs.get('SetStaticRoute', outputs.get('SetStaticRoute', None))
        MinIGPBGPRoute = inputs.get('MinIGPBGPRoute', outputs.get('MinIGPBGPRoute', None))
        nonMaxBGPLocalPref = inputs.get('nonMaxBGPLocalPref', outputs.get('nonMaxBGPLocalPref', None))
        BGPLocalPref = inputs.get('BGPLocalPref', outputs.get('BGPLocalPref', None))
        BGPRoute = inputs.get('BGPRoute', outputs.get('BGPRoute', None))
        MaxBGPLocalPrefBGPRoute = inputs.get('MaxBGPLocalPrefBGPRoute', outputs.get('MaxBGPLocalPrefBGPRoute', None))
        SetBGPLocalPref = inputs.get('SetBGPLocalPref', outputs.get('SetBGPLocalPref', None))
        IncomingFwdInterface = inputs.get('IncomingFwdInterface', outputs.get('IncomingFwdInterface', None))
        OutgoingFwdInterface = inputs.get('OutgoingFwdInterface', outputs.get('OutgoingFwdInterface', None))
        ConnectedNodes = inputs.get('ConnectedNodes', outputs.get('ConnectedNodes', None))
        Fwd = inputs.get('Fwd', outputs.get('Fwd', None))
        nonMinCostAD = inputs.get('nonMinCostAD', outputs.get('nonMinCostAD', None))
        SetAdminDist = inputs.get('SetAdminDist', outputs.get('SetAdminDist', None))
        minOSPFRouteCost = inputs.get('minOSPFRouteCost', outputs.get('minOSPFRouteCost', None))
        nonMinIGPCost = inputs.get('nonMinIGPCost', outputs.get('nonMinIGPCost', None))
        ConnectedBGPAnnouncement = inputs.get('ConnectedBGPAnnouncement', outputs.get('ConnectedBGPAnnouncement', None))
        MinAsPathBGPRoute = inputs.get('MinAsPathBGPRoute', outputs.get('MinAsPathBGPRoute', None))
        BGPAnnouncement = inputs.get('BGPAnnouncement', outputs.get('BGPAnnouncement', None))

        v1, v2, v3, v4, v5, v6 = z3.Consts('v1 v2 v3 v4 v5 v6', self.vertex)
        t1, t2, t3, t4 = z3.Consts('t1 t2 t3 t4', z3.IntSort())
        s1, s2, s3 = z3.Consts('s1 s2 s3', string_sort)

        connected_networks_used = False
        directly_connected_nodes_used = False

        check = constraints[:]
        if StaticRouteCost is not None:
            c = datatype_route_cost(StaticRouteCost, is_network, is_node, self.vertex)
            constraints.append(c)

        if IGPRouteCost is not None:
            c = datatype_route_cost(IGPRouteCost, is_network, is_node, self.vertex)
            constraints.append(c)

            # The cost of any not directly connected network is Zero
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(v1, v2, v3, t1),
                        self.connected_networks_f(v2, v1)),
                    t1 == 0))
            constraints.append(c)

            # The cost of any not directly connected network is more than zero
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(v1, v2, v3, t1),
                        z3.Not(self.connected_networks_f(v2, v1))),
                    t1 > 0))
            constraints.append(c)

        if MinIGPBGPRoute is not None:
            c = datatype_route_bgp(MinIGPBGPRoute, is_network, is_node,
                                   is_as_path_length, string_sort, self.vertex)
            constraints.append(c)
            # HACK: we assume all the BGP routes has the the same preference
            # HACK: we need to propagate properly the ASPath Length from the input
            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    MinIGPBGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.And(t1 == 3, t2 == 6)))
            constraints.append(c)


        if nonMinIGPCost is not None and IGPRouteCost is not None:
            c = z3.ForAll(
                [v1, v2, v3, v4, t1, t1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(v1, v2, v3, t1),
                        IGPRouteCost(v1, v2, v4, t2),
                        t2 < t1),
                    nonMinIGPCost(v2, v1, t2)))
            constraints.append(c)

        if BGPAnnouncement is not None and BGPRoute is not None:
            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    BGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.Exists(
                        [v4],
                        z3.And(
                            BGPAnnouncement(v4, v2, v3, s1, t1, t2),
                            self.connected_networks_f(v2, v4)
                        )
                    )
                ))
            constraints.append(c)

        if BestOSPFRoute is not None:
            connected_networks_used = True
            directly_connected_nodes_used = True
            c = datatype_route_cost(BestOSPFRoute, is_network, is_node, self.vertex)
            constraints.append(c)
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Not(
                        z3.Exists(
                            [v4, t2],
                            z3.And(BestOSPFRoute(v1, v2, v4, t2), t1 != t2)))))
            constraints.append(c)

            # Route cost should be larger than 0
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    t1 > 0))
            constraints.append(c)

            # Only one best BestOSPFRoute
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Not(
                        z3.Exists(
                            [v4, t2],
                            z3.And(
                                BestOSPFRoute(v1, v2, v4, t2),
                                v4 != v3)))))
            constraints.append(c)

            # If a route has BestOSPFRoute then the next hop should either have
            # a BestOSPFRoute for the given network or should be connected directly
            # to the given network
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Exists(
                        [v4, t2],
                        z3.Or(
                            z3.And(
                                BestOSPFRoute(v1, v3, v4, t2),
                                t2 < t1,
                                v4 != v2
                            ),
                            self.connected_networks_f(v3, v1)))))
            constraints.append(c)

            # Don't Forward directly connected networks
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Not(self.connected_networks_f(v2, v1))))
            constraints.append(c)
            
            # For a given router, BestOSPFRoute must forward any
            # given network to only one router
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Not(z3.Exists(
                        [v4, t2],
                        z3.And(
                            BestOSPFRoute(v1, v2, v4, t2),
                            v4 != v3
                        )))))
            constraints.append(c)

            # OSPF must use the same next hop cost
            # if the two networks are on the same destination router
            c = z3.ForAll(
                [v1, v2, v3, v4, v5, t1, t2],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        BestOSPFRoute(v1, v2, v3, t1),
                        BestOSPFRoute(v4, v2, v5, t2),
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [v6],
                            z3.And(
                                self.connected_networks_f(v6, v1),
                                self.connected_networks_f(v6, v4),
                            )),
                    ),
                    z3.And(v3 == v5, t1 == t2)
                )
            )
            constraints.append(c)

            # Only route to directly connected nodes
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    self.directly_connected_nodes(v2, v3)))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    t1 <= 20)
            )
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, v4, v5, v6, t1, t2, t3],
                z3.Implies(
                    z3.And(
                        BestOSPFRoute(v1, v2, v3, t1),
                        self.connected_networks_f(v3, v1),
                        BestOSPFRoute(v5, v2, v3, t2),
                        BestOSPFRoute(v5, v3, v6, t3),
                        v5 != v1
                    ),
                    t1 == t2 - t3
                )
            )
            constraints.append(c)

            # Ensure reasonable costs
            c = z3.ForAll(
                [v1, v2, v3, v4, v5, v6, t1, t2, t3, t4],
                z3.Implies(
                    z3.And(
                        BestOSPFRoute(v1, v2, v3, t1),
                        BestOSPFRoute(v1, v3, v4, t2),
                        BestOSPFRoute(v5, v2, v3, t3),
                        BestOSPFRoute(v5, v3, v6, t4),
                    ),
                    t1 - t2 == t3 - t4
                )
            )
            constraints.append(c)

        if OSPFRoute is not None:
            connected_networks_used = True
            directly_connected_nodes_used = True
            c = datatype_route_cost(OSPFRoute, is_network, is_node, self.vertex)
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    OSPFRoute(v1, v2, v3, t1),
                    z3.Exists(
                        [v4, t2],
                        z3.Or(
                            z3.And(
                                OSPFRoute(v1, v3, v4, t2),
                                t2 < t1,
                                v4 != v2
                            ),
                            self.connected_networks_f(v3, v1)))))
            #constraints.append(c)
            
            c = z3.ForAll(
              [v1, v2, v3, v4, t1, t2],
              z3.Implies(
                z3.And(                
                  OSPFRoute(v1, v2, v3, t1),
                  OSPFRoute(v1, v2, v4, t2)
                  ),
                  t1 == t2
                )
              )
            #constraints.append(c)

            # OSPF Route cost should be larger than 0
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    OSPFRoute(v1, v2, v3, t1),
                    t1 > 0))
            constraints.append(c)

            # OSPF must use the same next hop and cost
            # if the two networks are on the same destination router
            c = z3.ForAll(
                [v1, v2, v3, v4, v5, t1, t2],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        OSPFRoute(v1, v2, v3, t1),
                        OSPFRoute(v4, v2, v5, t2),
                        v3 == v5,
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [v6],
                            z3.And(
                                self.connected_networks_f(v6, v1),
                                self.connected_networks_f(v6, v4),
                            )),
                    ),
                    z3.And(t1 == t2)
                )
            )
            constraints.append(c)

            # Only route to directly connected nodes
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    OSPFRoute(v1, v2, v3, t1),
                    self.directly_connected_nodes(v2, v3)))
            #constraints.append(c)


        if SetStaticRouteCost is not None:
            c = datatype_route_cost(SetStaticRouteCost, is_network, is_node, self.vertex)
            constraints.append(c)

        if not(Node is None or Network is None or Interface is None):
            c = datatypes_unique(self.vertex, [Node, Interface, Network])
            constraints.append(c)
        if EdgePhy is not None:
            c = z3_interface_links(self.vertex, is_interface, EdgePhy)
            constraints.append(c)

        if Node is not None:
            for v in self.all_vertices:
                if str(v) in self.node_names:
                    constraints.append(Node(v) == True)
                else:
                    constraints.append(Node(v) == False)
        if Network is not None:
            for v in self.all_vertices:
                if str(v) in self.network_names:
                    constraints.append(Network(v) == True)
                else:
                    constraints.append(Network(v) == False)

        if Interface is not None:
            for v in self.all_vertices:
                if str(v) in self.interface_names:
                    constraints.append(Interface(v) == True)
                else:
                    constraints.append(Interface(v) == False)

        if EdgePhy is not None:
            for src in self.network_graph.nodes():
                src_v = self.get_vertex(src)
                for dst in self.network_graph.nodes():
                    dst_v = self.get_vertex(dst)
                    if self.network_graph.has_edge(src, dst):
                        constraints.append(EdgePhy(src_v, dst_v) == True)
                    else:
                        constraints.append(EdgePhy(src_v, dst_v) == False)
            c = z3.ForAll([v1, v2], z3.Implies(EdgePhy(v1, v2), EdgePhy(v2, v1)))
            constraints.append(c)

        if ConnectedNodes is not None:
            pairs = [[self.get_vertex(v) for v in p] for p in self.connected_nodes]
            c = z3.ForAll(
                [v1, v2, v3, v4],
                ConnectedNodes(v1, v2, v3, v4) == z3.Or(
                *[z3.And(v1 == p[0], v2 == p[1], v3 == p[2], v4 == p[3]) for p in pairs]))
            constraints.append(c)

        if nonMinOSPFRouteCost is not None and OSPFRoute is not None:
            c = z3.ForAll(
                [v1, v2, t1],
                z3.Implies(
                    nonMinOSPFRouteCost(v1, v2, t1),
                    z3.Exists([v3], OSPFRoute(v1, v2, v3, t1))))
            constraints.append(c)
            
            c = z3.ForAll(
                [v1, v2, t1],
                nonMinOSPFRouteCost(v1, v2, t1) ==
                z3.Exists(
                  [v3, v4, t2],
                  z3.And(
                    OSPFRoute(v1, v2, v3, t1),
                    OSPFRoute(v1, v2, v4, t2),
                    t2 < t1
                  )
                )
              )
            constraints.append(c)

        if BestOSPFRoute is not None and nonMinOSPFRouteCost is not None:
            # Best route must be the min set
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    z3.Not(nonMinOSPFRouteCost(v1, v2, t1))))
            constraints.append(c)

        if minOSPFRouteCost is not None and BestOSPFRoute is not None:
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    BestOSPFRoute(v1, v2, v3, t1),
                    minOSPFRouteCost(v1, v2, t1)))
            constraints.append(c)

        if minOSPFRouteCost is not None and nonMinOSPFRouteCost is not None:
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    minOSPFRouteCost(v1, v2, t1),
                    z3.Not(nonMinOSPFRouteCost(v1, v2, t1))))
            constraints.append(c)

        if SetAdminDist is not None:
            # Set Admin Distance only once
            c = z3.ForAll(
                [v1, s1, t1],
                z3.Implies(
                    SetAdminDist(v1, s1, t1),
                    z3.Not(z3.Exists([t2], z3.And(SetAdminDist(v1, s1, t2), t1 != t2)))))
            constraints.append(c)

        if nonMinCostAD is not None:
            c = z3.ForAll(
                [v1, v2, s1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(v1, v2, t1),
                        is_announced_network(v1)
                    ), t1 == 2))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, s1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(v1, v2, t1),
                        z3.Not(is_announced_network(v1))
                    ), z3.Or(t1 == 1, t1 == 3)))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, s1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(v1, v2, t1),
                    ), t1 == 3))

            constraints.append(c)

        if nonMinCostAD is not None and SetAdminDist is not None and Route is not None:
            c = z3.ForAll(
                [v1, v2, v3, v4, s1, s2, t1],
                #z3.Implies(
                    z3.And(
                        Route(v1, v2, v3, s1),
                        Route(v1, v2, v4, s2),
                        s1 != s2,
                        SetAdminDist(v2, s1, t1),
                        SetAdminDist(v2, s2, t2),
                        t1 < t2
                    ) ==
                        nonMinCostAD(v1, v2, t2)
                )#)
            constraints.append(c)

        if nonMinCostAD is not None and SetAdminDist is not None and Route is not None:

            c = z3.ForAll(
                [v1, v2, t1],
                nonMinCostAD(v1, v2, t1) == z3.Exists(
                    [s1, s2, v3, t2],
                    z3.And(
                        SetAdminDist(v2, s1, t1),
                        Route(v1, v2, v3, s2),
                        SetAdminDist(v2, s2, t2),
                        t2 < t1
                    ))
            )
            constraints.append(c)

        if Fwd is not None:
            print 'HEY'
            c = z3.ForAll(
                [v1, v2, v3, v4, s1, s2],
                z3.Implies(
                    z3.And(Fwd(v1, v2, v3, s1),
                           Fwd(v1, v2, v4, s2)),                          
                                 z3.And(v4 == v3, s1 == s2)))
            constraints.append(c)

        if OSPFRoute is not None or BestOSPFRoute is not None:
            if OSPFRoute is not None:
                func = OSPFRoute
            elif BestOSPFRoute is not None:
                func = BestOSPFRoute
            # Block announced networks from being advertised over OSPF
            c = z3.ForAll(
                [v1, v2, v3, t1],
                z3.Implies(
                    is_announced_network(v1),
                    z3.Not(func(v1, v2, v3, t1))))
            constraints.append(c)

        if ConnectedBGPAnnouncement is not None:
            connected_networks_used = True
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    ConnectedBGPAnnouncement(v1, v2, v3),
                    self.connected_networks_f(v1, v2)))
            constraints.append(c)

        if ConnectedBGPAnnouncement is not None and MaxBGPLocalPrefBGPRoute is not None:
            pass
            connected_networks_used = True
            c = z3.ForAll(
                [v1, v2, v3],
                ConnectedBGPAnnouncement(v1, v2, v3) == z3.Exists(
                    [s1, t1, t2],
                    z3.And(
                        MaxBGPLocalPrefBGPRoute(v1, v2, v3, s1, t1, t2),
                        self.connected_networks_f(v1, v2)
                    )
                )
            )
            #constraints.append(c)

        if nonMaxBGPLocalPref is not None and BGPLocalPref is not None:
            c = z3.ForAll(
                [v1, v2, v3, t1],
                nonMaxBGPLocalPref(v3, t1) == z3.And(
                    BGPLocalPref(v1, v2, v3, t1),
                    z3.Exists(
                        [v4, v5, t2],
                        z3.And(BGPLocalPref(v4, v5, v3, t2), t1 < t2))

                    ))
            constraints.append(c)

        if MaxBGPLocalPrefBGPRoute is not None and BGPLocalPref is not None:
            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    MaxBGPLocalPrefBGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.And(
                        BGPLocalPref(v1, v2, v3, t2),
                        z3.Not(
                            z3.Exists(
                                [v4, v5, t3],
                                z3.And(BGPLocalPref(v4, v5, v3, t3), t3 > t2))))))
            constraints.append(c)

            #if BGPLocalPref is not None:
            #     #connected_networks_used = True
            #    c = z3.ForAll(
            #         [v1, v2, v3, t1],
            #        z3.Implies(
            #            BGPLocalPref(v1, v2, v3, t1),
            #            z3.And(
            #                self.connected_networks_f(v1, v2),
            #                is_announced_network(v3),
            #            )
            #        )
            #    )
            #    constraints.append(c)

        if MaxBGPLocalPrefBGPRoute is not None:
            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    MaxBGPLocalPrefBGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.Not(
                        z3.Exists(
                            [v4, t3, t4],
                            z3.And(
                                MaxBGPLocalPrefBGPRoute(v4, v2, v3, s2, t3, t4),
                                t2 < t4
                            )
                        ))))
            constraints.append(c)

        if BGPRoute is not None and BGPLocalPref is not None:
            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    BGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.Exists([v4, t2], BGPLocalPref(v4, v2, v3, t2))))
            constraints.append(c)

        if SetNetwork is not None:
            c = z3.ForAll(
                [v1, v2],
                z3.Implies(
                    SetNetwork(v1, v2) == True,
                    z3.Not(
                        z3.Exists(
                            [v3],
                            z3.And(
                                v3 != v1,
                                z3.Or(SetNetwork(v3, v2), SetNetwork(v2, v3)))))))
            constraints.append(c)

        if SetInterface is not None:
            c = z3.ForAll(
                [v1, v2],
                z3.Implies(
                    SetInterface(v1, v2) == True,
                    z3.Not(
                        z3.Exists(
                            [v3],
                            z3.And(
                                v3 != v1,
                                z3.Or(SetInterface(v3, v2), SetInterface(v2, v3)))))))
            constraints.append(c)

        if SetLink is not None:
            c = z3.ForAll(
                [v1, v2],
                 z3.Not(
                     z3.And(
                         SetLink(v1, v2),
                         z3.Exists(
                             [v3],
                             z3.And(
                                 z3.Distinct(v1, v2, v3),
                                 z3.Or(SetLink(v1, v3),
                                       SetLink(v3, v1)))))))
            constraints.append(c)

        if LinkOSPF is not None:
            c = z3.ForAll(
                [v1, v2, t1],
                z3.Implies(
                    LinkOSPF(v1, v2, t1),
                    z3.Exists(
                        [v3, v4],
                        z3.And(
                            EdgePhy(v1, v3),
                            EdgePhy(v3, v4),
                            SetOSPFEdgeCost(v3, v4, t1),
                            EdgePhy(v4, v2)))))
            constraints.append(c)

        if SetOSPFEdgeCost is not None and EdgePhy is not None:
            c = z3.ForAll(
                [v1, v2, t1],
                z3.Implies(
                    SetOSPFEdgeCost(v1, v2, t1),
                    EdgePhy(v1, v2)))
            constraints.append(c)
            c = z3.ForAll(
                [v1, v2, t1],
                z3.Implies(
                    SetOSPFEdgeCost(v1, v2, t1),
                    z3.Not(z3.Exists([t2], z3.And(SetOSPFEdgeCost(v1, v2, t2), t1 != t2)))))
            constraints.append(c)

        if Route is not None:
            connected_networks_used = True
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Route(v1, v2, v3, s1),
                    v2 != v3))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    z3.And(
                        Route(v1, v2, v3, s1),
                        is_announced_network(v1)
                    ), s1 == get_string_const_val('bgp')))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    z3.And(
                        Route(v1, v2, v3, s1),
                        z3.Not(is_announced_network(v1))
                    ), s1 != get_string_const_val('bgp')))
            constraints.append(c)

            # Have continueous OSPFRoutes
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    z3.And(Route(v1, v2, v3, s1), s1 == get_string_const_val('ospf')),
                    z3.Exists(
                        [v4],
                        z3.Or(
                            z3.And(
                                Route(v1, v3, v4, s1),
                                v4 != v2
                            ),
                            self.connected_networks_f(v3, v1)))))
            # Long
            constraints.append(c)


            # Compute OSPF routes for all not directly connnect networks
            c = z3.ForAll(
                [v1, v2],
                z3.Or(
                    z3.Not(z3.And(is_node(v2), is_network(v1))),
                    z3.And(self.connected_networks_f(v2, v1), z3.Not(is_announced_network(v1))),
                    z3.Exists(
                        [v3],
                        Route(v1, v2, v3, get_string_const_val('ospf')),
                    )))
            constraints.append(c)

            # There should be no more than one route for the same network,
            # the same protocol, the same router
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Route(v1, v2, v3, s1),
                    z3.Not(z3.Exists(
                        [v4],
                        z3.And(
                            Route(v1, v2, v4, s1),
                            v4 != v3
                        )))))
            # Long
            constraints.append(c)

            # OSPF must use the same next hop if the two networks are on the same
            # destination router
            c = z3.ForAll(
                [v1, v2, v3, v4, v5, s1],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        Route(v1, v2, v3, s1),
                        Route(v4, v2, v5, s1),
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [v6],
                            z3.And(
                                self.connected_networks_f(v6, v1),
                                self.connected_networks_f(v6, v4),
                            )),
                        s1 == get_string_const_val('ospf'),
                    ),
                    v3 == v5
                )
            )
            # Long
            constraints.append(c)

            directly_connected_nodes_used = True
            # Only route to directly connected nodes
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Route(v1, v2, v3, s1),
                    self.directly_connected_nodes(v2, v3)))
            constraints.append(c)

        if Fwd is not None:
            connected_networks_used = True
            ## Use only static routes
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Fwd(v1, v2, v3, s1),
                    s1 == get_string_const_val('static')
                )
            )
            #constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(Fwd(v1, v2, v3, s1), v2 != v3))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    z3.And(
                        Fwd(v1, v2, v3, s1),
                        is_announced_network(v1)
                    ), s1 == get_string_const_val('bgp')))
            constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    z3.And(
                        Fwd(v1, v2, v3, s1),
                        z3.Not(is_announced_network(v1))
                    ), s1 != get_string_const_val('bgp')))
            constraints.append(c)

            directly_connected_nodes_used = True
            # Next hop can be only directly connected node
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Fwd(v1, v2, v3, s1),
                    self.directly_connected_nodes(v2, v3)
                ))
            constraints.append(c)

            # Only forward to one destination
            #c = z3.ForAll(
            #    [v1, v2, v3, s1],
            #    z3.Implies(
            #        Fwd(v1, v2, v3, s1),
            #        z3.Not(
            #            z3.Exists(
            #                [v4, v5, v6, s2],
            #                 z3.And(Fwd(v4, v5, v6, s2), v1 == v4, v2 == v5, v6 != v3, s1 == s2)))))
            #constraints.append(c)

            # Don't forward backward
            #c = z3.ForAll(
            #    [v1, v2, v3, s1],
            #    z3.Implies(
            #        Fwd(v1, v2, v3, s1),
            #        z3.Not(
            #            z3.Exists(
            #                [v4, v5, v6, s2],
            #                z3.And(Fwd(v4, v5, v6, s2), v1 == v4, v2 == v6,
            #                      v3 == v5, s1 == s2)))))
            #constraints.append(c)
            # Don't Forward directly connected networks
            c = z3.ForAll(
                [v1, v2, v3, s1],
                z3.Implies(
                    Fwd(v1, v2, v3, s1),
                    z3.Not(
                        self.connected_networks_f(v2, v1))))
            constraints.append(c)

            # IF two networks are connected to the same router
            # then they must have the same Forwarding entry for a given
            # Protocol
            #c = z3.ForAll(
            #    [v1, v2, v3, v4, s1],
            #    z3.Implies(
            #        z3.And(
            #            Fwd(v1, v2, v3, s1),
            #            Fwd(v3, v2, v4, s1),
                        #v2 != self.get_vertex('A'),
            #            z3.Exists(
            #                [v5],
            #                z3.And(
            #                    self.connected_networks_f(v5, v1),
            #                    self.connected_networks_f(v5, v3),
            #                    v5 != v2
            #                ))
            #        ), v3 == v4))
            #constraints.append(c)

        #if OutgoingFwdInterface is not None and Fwd is not None:
        #    # Fwd entry must exists on the router to output the packet
        #    c = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            OutgoingFwdInterface(v1, v2, v3),
        #            z3.Exists([v4, s1], Fwd(v1, v2, v4, s1))))
        #    constraints.append(c)

        if MinAsPathBGPRoute is not None:
            connected_networks_used = True
            directly_connected_nodes_used = True

            bgp_nets = []
            not_bgp_nets = []
            for net in self.network_names:
                if 'BGP' in net:
                    bgp_nets.append(self.get_vertex(net))
                else:
                    not_bgp_nets.append(self.get_vertex(net))
            for net in not_bgp_nets:
                c = z3.Not(z3.Exists(
                    [v1, v2, v3, s1, t1, t2],
                    z3.And(
                        MinAsPathBGPRoute(v1, v2, v3, s1, t1, t2),
                        v2 == net)
                ))
                #constraints.append(c)

            c = z3.ForAll(
                [v1, v2, v3, s1, t1, t2],
                z3.Implies(
                    MinAsPathBGPRoute(v1, v2, v3, s1, t1, t2),
                    z3.And(
                        z3.Not(self.connected_networks_f(v2, v1)),
                        z3.Or(*[v2 == net for net in bgp_nets]))
            ))
            #constraints.append(c)

        if OutgoingFwdInterface is not None and Fwd is not None and ConnectedNodes is not None:
            # Fwd entry must exists on the router to output the packet
            c = z3.ForAll(
                [v1, v2, v3],
                OutgoingFwdInterface(v1, v2, v3) == z3.Exists(
                    [v4, s1, v5],
                    z3.And(
                        Fwd(v1, v2, v4, s1),
                        ConnectedNodes(v2, v3, v5, v4))))
            constraints.append(c)

        if OutgoingFwdInterface is not None and Interface is not None:
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    OutgoingFwdInterface(v1, v2, v3),
                    Interface(v3)))
            constraints.append(c)

        if IncomingFwdInterface is not None and Fwd is not None and ConnectedNodes is not None:
            # Fwd entry must exists on a PREVIOUS router to output the packet
            # to this router
            c = z3.ForAll(
                [v1, v2, v3],
                IncomingFwdInterface(v1, v2, v3) == z3.Exists(
                    [v4, s1, v5],
                    z3.And(Fwd(v1, v4, v3, s1),
                           ConnectedNodes(v4, v5, v2, v3))))
            constraints.append(c)

        if OutgoingFwdInterface is not None:
            # Only one outgoing interface
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    OutgoingFwdInterface(v1, v2, v3),
                    z3.Not(
                        z3.Exists(
                            [v4, v5, v6],
                            z3.And(OutgoingFwdInterface(v4, v5, v6), v4 == v1, v5 == v2, v6 != v3)
                        ))))
            constraints.append(c)

        if OutgoingFwdInterface is not None and EdgePhy is not None:
            # Only have OutgoingFwdInterface through interfaces connected
            # directly to the router
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    OutgoingFwdInterface(v1, v2, v3),
                    EdgePhy(v2, v3)))
            constraints.append(c)

        if IncomingFwdInterface is not None and EdgePhy is not None:
            # Only have IncomingFwdInterface through interfaces connected
            # directly to the router
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    IncomingFwdInterface(v1, v2, v3),
                    EdgePhy(v2, v3)))
            constraints.append(c)

        if OutgoingFwdInterface is not None and IncomingFwdInterface is not None:
            # If an interface is marked as outgoing then it cannot be incomming as well
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    OutgoingFwdInterface(v1, v2, v3),
                    z3.Not(IncomingFwdInterface(v1, v3, v2))))
            constraints.append(c)

            # If an interface is marked as incoming then it cannot be outgoing as well
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    IncomingFwdInterface(v1, v2, v3),
                    z3.Not(OutgoingFwdInterface(v1, v3, v2))))
            constraints.append(c)

        if OutgoingFwdInterface is not None and EdgePhy is not None and IncomingFwdInterface is not None:
            # If the router is not a terminating for the given network,
            # The must have IncomingFwdInterface
            # TODO(AH): NOT WORKING RIGHT NOW
            c = z3.ForAll(
                [v1, v2, v3],
                z3.Implies(
                    z3.And(
                        OutgoingFwdInterface(v1, v2, v3),
                        z3.Not(EdgePhy(v1, v2))),
                    z3.Exists(
                        [v4, v5, v6],
                        z3.And(IncomingFwdInterface(v4, v5, v6), v4 == v1, v6 == v2, v4 != v3))))
            #constraints.append(c)
        if box_name == 'ibgp08':
            #constraints = []
            pass
        for name, func in BOXES[box_name]['inputs'].iteritems():
            func_const = self.generate_function_constraints(func)
            #if name in ['MinAsPathBGPRoute']: continue
            constraints.append(func_const)
        for name, func in BOXES[box_name]['outputs'].iteritems():
            func_const = self.generate_function_constraints(func)
            #print "OUTPUT", name, func_const
            #if name in ['OutgoingFwdInterface',
            #            'IncomingFwdInterface']: continue
            constraints.append(func_const)

        if directly_connected_nodes_used:
            constraints.extend(self.fill_directly_connected_nodes())
        if connected_networks_used:
            constraints.extend(self.fill_connected_networks_f())
        BOXES[box_name]['input_constraints'] = constraints

    def read_init_inputs(self):
        """Add initial inputs as constraints to the solvers"""
        skipped = []
        self.bgp_annoucements = []
        for box_name in self.boxes_names:
            for op, name, args in self.init_inputs:
                func_true_vals = []
                parsed_args = []
                if name not in BOXES[box_name]['inputs']:
                    skipped.append(name)
                    continue
                func = BOXES[box_name]['inputs'][name]
                assert func.arity() == len(args), "%s %s" % (func, args)
                for i, arg in enumerate(args):
                    domain = str(func.domain(i))
                    if domain == 'Vertex':
                        parsed_arg = self.get_vertex(arg)
                    elif domain.startswith('BitVec'):
                        parsed_arg = get_string_const_val(arg)
                    elif domain == 'Int':
                        parsed_arg = int(arg)
                    else:
                        raise ValueError(
                            "Unrecognized argument type '%s' for '%s'" % (domain, arg))
                    parsed_args.append(parsed_arg)
                if name == 'BGPAnnouncement':
                    self.bgp_annoucements.append(parsed_args)
                if name not in self.fixed_inputs:
                    self.fixed_inputs[name] = []
                if op == '+':
                    f = (func(parsed_args) == True)
                    func_true_vals.append(parsed_args + [z3.BoolVal(True)])
                else:
                    f = (func(parsed_args) == False)
                BOXES[box_name]['fixed_inputs'].append(f)
                #print "PROCESESS " * 50
                process = self._process_vals(func, func_true_vals + ['False'],
                                   BOXES[box_name]['inputs'])
                #print process
                #BOXES[box_name]['fixed_inputs'].extend(process)
                self.fixed_inputs[name].append(f)

        # Make sure we read everything
        #not_read = set([name for name, args in self.init_inputs]) - set(skipped)
        #assert not not_read, "Did not read %s" % not_read

    def read_fixed_outputs(self, outputs):
        skipped = []
        parsed_outputs = parse_inputs(outputs)
        self.fixed_best_ospf = []
        for box_name in self.boxes_names:
            for op, name, args in parsed_outputs:
                parsed_args = []
                if name not in BOXES[box_name]['outputs']:
                    skipped.append(name)
                    continue
                func = BOXES[box_name]['outputs'][name]
                assert func.arity() == len(args), "%s %s" % (func, args)
                for i, arg in enumerate(args):
                    domain = str(func.domain(i))
                    if domain == 'Vertex':
                        parsed_arg = self.get_vertex(arg)
                    elif domain.startswith('BitVec'):
                        parsed_arg = get_string_const_val(arg)
                    elif domain == 'Int':
                        parsed_arg = int(arg)
                    else:
                        raise ValueError(
                            "Unrecognized argument type '%s' for '%s'" % (
                                domain, arg))
                    parsed_args.append(parsed_arg)
                if name not in self.fixed_inputs:
                    self.fixed_inputs[name] = []
                if op == '+':
                    f = (func(parsed_args) == True)
                    if name == 'BestOSPFRoute':
                        self.fixed_best_ospf.append(
                            OSPFSyn.BestOSPFRoute(args[0], args[1], args[2],
                                                  args[3]))
                else:
                    f = (func(parsed_args) == False)
                BOXES[box_name]['fixed_outputs'].append(f)
                self.fixed_inputs[name].append(f)
        # Make sure we read everything
        #assert not set([name for name, args in parsed_outputs]) - set(skipped)

    def get_vertex(self, name):
        """Takes a name string and returns the corresponding Z3 object"""
        if isinstance(name, int):
            name = str(name)
        if isinstance(name, basestring):
            return self.name_to_vertex[name]
        else:
            return name

    def get_name(self, vetrex):
        """Takes a Z3 object and returns the corresponding name string """
        inv_map = {v: k for k, v in self.name_to_vertex.items()}
        return inv_map[vetrex]

    def _get_names(self):
        node_names = []
        interface_names = []
        network_names = []
        as_paths = []
        announced_network_names = []
        as_paths_length = {}
        self.connected_networks = []
        for op, func_name, args in self.init_inputs:
            if func_name in ['SetNode', 'Node', 'SetInterface', 'SetNetwork',
                             'SetBGPAnnouncement', 'SetBGPLocalPref',
                             'SetBGPLocalPref']:
                node_names.append(args[0])
            if func_name in ['SetInterface']:
                interface_names.append(args[1])
                self.node_interface.append((args[0], args[1]))
            if func_name in ['SetNetwork']:
                network_names.append(args[1])
                self.node_network.append((args[0], args[1]))
                self.connected_networks.append((args[0], args[1]))
            if func_name in ['SetLink']:
                interface_names.append(args[0])
                interface_names.append(args[1])
                self.links.append((args[0], args[1]))
            if func_name in ['SetBGPAnnouncement']:
                edge = args[0]
                net = args[1]
                ext = args[2]
                path = args[3]
                pathlength = int(args[4])
                if edge not in self.set_bgp_annoucement:
                    self.set_bgp_annoucement[edge] = []
                print "Setting", (edge, net, ext, path, pathlength)
                self.set_bgp_annoucement[edge].append((edge, net, ext, path, pathlength))
                # network_names.append(args[2])
                as_paths.append(args[3])
                as_paths_length[args[3]] = int(args[4])
                announced_network_names.append(args[2])
                self.connected_networks.append((args[0], args[2]))
        # Make unique
        node_names = list(set(node_names))
        interface_names = list(set(interface_names))
        network_names = list(set(network_names))
        self.as_paths = list(set(as_paths))
        self.announced_network_names = list(set(announced_network_names))
        for as_path in self.as_paths:
            as_paths_length[get_string_const_val(as_path)] = as_paths_length[as_path]
            del as_paths_length[as_path]
        self.as_paths_length = as_paths_length
        return node_names, interface_names, network_names, announced_network_names

    def _create_vertices(self, vertex_name):
        node_names, interface_names, network_names, announced_network_names = self._get_names()
        self.node_names = node_names
        self.interface_names = interface_names
        self.network_names = network_names
        all_names = node_names + interface_names + network_names + announced_network_names
        (vertex, all_vertices) = z3.EnumSort(vertex_name, all_names)
        self.vertex = vertex
        self.all_vertices = all_vertices
        translator.LB_TYPE_TO_Z3_TYPE['Vertex'] = self.vertex
        self.name_to_vertex = dict((str(v), v) for v in self.all_vertices)
        translator.STRING_TO_VERTEX = self.name_to_vertex
        self.nodes = [self.get_vertex(name) for name in node_names]
        self.interfaces = [self.get_vertex(name) for name in interface_names]
        self.networks = [self.get_vertex(name) for name in network_names]
        self.announced_networks = [self.get_vertex(name) for name in self.announced_network_names]

    def construct_input_graph(self):
        for node in self.node_names:
            self.network_graph.add_node(node, **{VERTEX_TYPE: NODE_TYPE})
        for network in self.network_names:
            self.network_graph.add_node(network, **{VERTEX_TYPE: NETWORK_TYPE})
        for interface in self.interface_names:
            self.network_graph.add_node(interface, **{VERTEX_TYPE: INTERFACE_TYPE})
        for node, interface in self.node_interface:
            self.network_graph.add_edge(node, interface, **{VERTEX_TYPE: INTERNAL_EDGE})
            self.network_graph.add_edge(interface, node, **{VERTEX_TYPE: INTERNAL_EDGE})
        for node, network in self.node_network:
            self.network_graph.add_edge(node, network, **{VERTEX_TYPE: NETWORK_TYPE})
            self.network_graph.add_edge(network, node, **{VERTEX_TYPE: NETWORK_TYPE})
        for src, dst in self.links:
            self.network_graph.add_edge(src, dst, **{VERTEX_TYPE: LINK_EDGE})
            self.network_graph.add_edge(dst, src, **{VERTEX_TYPE: LINK_EDGE})

        iface_node = {}
        self.connected_nodes = []
        for node, interface in self.node_interface:
            iface_node[interface] = node
        for siface, diface in self.links:
            snode = iface_node[siface]
            dnode = iface_node[diface]
            self.connected_nodes.append([snode, siface, diface, dnode])
            self.connected_nodes.append([dnode, diface, siface, snode])

    def parse_initial_inputs(self, inputs):
        self.init_inputs = parse_inputs(inputs)

    def gen_configs(self, outdir):
        print "Generating router configs"
        from gen_configs import GNS3TopologyGen
        from graph_util import get_bgp_attrs
        from graph_util import SetAnnouncement
        from graph_util import SetExternalPeer
        from graph_util import add_bgp_external_peer
        from graph_util import add_input_filter
        from graph_util import add_bgp_neighbor
        from graph_util import add_ip_prefix_list
        from graph_util import IPList


        g = nx.DiGraph()
        is_network = lambda g, node: g.node[node][VERTEX_TYPE] == NETWORK_TYPE
        is_router = lambda g, node: g.node[node][VERTEX_TYPE] == NODE_TYPE
        gen_ospf = len(self.ospf_costs) != 0
        gen_bgp = len(self.set_bgp_annoucement) != 0
        #assert gen_bgp, self.set_bgp_annoucement
        peering_nets = []

        announcements = []
        external_peers = []
        peer_asnums = {}
        origins_asnums = {}
        nextpeer_asnum = 20
        nextorigin_asnum = 1000

        for node, data in self.network_graph.nodes_iter(data=True):
            if is_network(self.network_graph, node) or is_router(self.network_graph, node):
                g.add_node(node, **data)
                get_bgp_attrs(g, node)['asnum'] = 10
                if node in self.static_routes:
                    if 'static_routes' not in g.node[node]:
                        g.node[node]['static_routes'] = []
                    g.node[node]['static_routes'].extend(self.static_routes[node])
                if node in self.set_bgp_annoucement:
                    for _, net, ext, path, pathlength in self.set_bgp_annoucement[node]:
                        if net not in peer_asnums:
                            peer_asnums[net] = nextpeer_asnum
                            nextpeer_asnum += 10
                        external_peers.append(SetExternalPeer(net, peer_asnums[net], node))
                        if ext not in origins_asnums:
                            origins_asnums[ext] = nextorigin_asnum
                            nextorigin_asnum += 10
                        #def add_ip_prefix_list(g, node, iplist):
                        peername = 'AS%d' % peer_asnums[net]
                        attrs = {
                            VERTEX_TYPE: PEER_TYPE,
                            'bgp': {'asnum': peer_asnums[net], 'neighbors': {}, 'announces': {}}
                        }
                        if not g.has_node(peername):
                            g.add_node(peername, **attrs)
                        add_bgp_neighbor(g, node, peername)
                        listname = '%sIPList' % ext
                        iplist = IPList(listname, [ext], 'permit')
                        add_ip_prefix_list(g, node, iplist)
                        match = 'ip address prefix %s ' %  listname
                        add_input_filter(g, node, peername,
                                         access='permit', match=match,
                                         action='set local-preference 200')

                        announcements.append(SetAnnouncement(ext, net, node, origins_asnums[ext]))
                        peering_nets.append(net)
                        # g, node, neighbor, access, match, action, lineno = None)
        if gen_bgp:
            for nodeA in self.network_graph.nodes_iter():
                if not is_router(self.network_graph, nodeA): continue
                for nodeB in self.network_graph.nodes_iter():
                    if not is_router(self.network_graph, nodeB): continue
                    if nodeA == nodeB: continue
                    add_bgp_neighbor(g, nodeA, nodeB)

        for src, dst, attrs in self.network_graph.edges_iter(data=True):
            t = (self.network_graph.node[src][VERTEX_TYPE],
                 self.network_graph.node[dst][VERTEX_TYPE])
            if t == (NODE_TYPE, NETWORK_TYPE):
                g.add_edge(src, dst, **dict(EDGE_TYPE=NETWORK_TYPE))
                g.add_edge(dst, src, **dict(EDGE_TYPE=NETWORK_TYPE))
            elif t == (INTERFACE_TYPE, INTERFACE_TYPE):
                srouter = [i for i in self.network_graph.neighbors(src) if is_router(self.network_graph, i)][0]
                drouter = [i for i in self.network_graph.neighbors(dst) if is_router(self.network_graph, i)][0]
                g.add_edge(srouter, drouter, edge_type=INTERNAL_EDGE)
                if gen_ospf:
                    cost = self.ospf_costs.get((src, dst), None)
                    if cost is None:
                        cost = 65530
                    else:
                        cost = cost.as_long()
                    g[srouter][drouter]['ospf_cost'] = cost

        peering_nets = list(set(peering_nets))
        addrmap = {'GOOGLE': u'8.8.0.0/16'}
        for i, net in enumerate(peering_nets):
            if g.has_node(net): g.remove_node(net)
            addrmap[net] = u'10.10.%d.0/31' % i
        for i, net in enumerate(sorted([n for n in self.network_names if n not in addrmap])):
            # if 'BGP' in net: continue
            addrmap[net] = u'192.168.%d.0/24' % i

        GNS3TopologyGen(g, addrmap,
                        bgp_announcements=announcements,
                        external_peers=external_peers,
                        workingdir='.',
                        outdir=outdir,
                        gen_ospf=gen_ospf, gen_bgp=gen_bgp)


def main():
    parser = argparse.ArgumentParser(description='Synthesize network config.')
    parser.add_argument("-i", required=True, dest="initial_inputs", help="Initial inputs file")
    parser.add_argument("-r", required=True, dest="fixed_outputs", help="Requirements file")
    parser.add_argument("-m", required=False, dest="mode", default='bgp', help="OSPF/BGP/Static mode")
    parser.add_argument("-u", dest="unrolling_limit", default=5, type=int,
                        help="Unrolling limit")
    args = parser.parse_args()
    with open(args.initial_inputs) as f:
        initial_inputs = f.read()
    with open(args.fixed_outputs) as f:
        fixed_outputs = f.read()
    if args.mode == 'bgp':
      BOXES_ORDER = ['ibgp03', 'ibgp04', 'ibgp05', 'ibgp06', 'ibgp07', 'ibgp08', 'ibgp09','ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']
    elif args.mode == 'ospf':
      BOXES_ORDER = ['ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']      
    elif args.mode == 'static':
      BOXES_ORDER = ['fwd01-0-static', 'fwd01-1-static']
      BOXES_ORDER = ['fwd01-1-static']
    else:
      raise NameError('Unknown synthesis mode')
    
    syn = Synthesizer(BOXES_ORDER, initial_inputs, fixed_outputs,
                      unrolling_limit=args.unrolling_limit)
    
    syn.synthesize()

if __name__ == '__main__':
    main()
