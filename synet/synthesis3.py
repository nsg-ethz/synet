#!/usr/bin/env python

import itertools
import tempfile

import networkx as nx
import z3

from synet.common import INTERFACE_TYPE
from synet.common import INTERNAL_EDGE
from synet.common import LINK_EDGE
from synet.common import NETWORK_TYPE
from synet.common import NODE_TYPE
from synet.common import PEER_TYPE
from synet.common import VERTEX_TYPE
from synet.translation import translator
from synet.translation.translator import Translator
from synet.translation.translator import get_string_const_val
from synet.utils import FUNCS_SIG
from synet.utils import fill_box_info
from synet.utils import get_original_version
from synet.utils import get_unrolled_version
from synet.utils import parse_inputs


__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"


MAX_OSPF_COST = 30
MAX_INT_VAL = 17


class Synthesizer(object):
    def __init__(self, boxes, boxes_names, inputs, fixed_outputs, unrolling_limit=5):
        self.boxes = boxes
        self.boxes_names = boxes_names
        self.init_inputs = []
        self.node_interface = []
        self.node_network = []
        self.links = []
        self.protocols = []
        self.as_paths = []
        self.fixed_inputs = {}
        # Holds partial evaluation constrains for connected networks
        self._tmp_connected_networks = []
        # Holds partial evaluation constrains for directly connected nodes
        self._tmp_dnodes = []
        self.connected_nodes = []  # Holds (node, iface, iface, node)
        self.parse_initial_inputs(inputs)
        self.set_bgp_annoucement = {}
        self._create_vertices()
        self.network_graph = nx.DiGraph()
        self.unrolling_limit = unrolling_limit
        self.ospf_costs = {}
        self.static_routes = {}

        for box_name in self.boxes:
            fill_box_info(self.boxes, box_name, unrolling_limit)

        self.read_init_inputs()
        self.read_fixed_outputs(fixed_outputs)
        self.construct_input_graph()
        #draw(self.network_graph, '/tmp/gg.ddot')
        self._fill_boxes()

    def build_dependency_graph(self):
        """
        Build dependency graph between the different boxes
        This is not used anywhere, however very helpful for debugging
        """
        self.dep_g = nx.DiGraph()
        for box_name in self.boxes_names:
            self.dep_g.add_node(box_name)
        for src in self.boxes_names:
            for dst in self.boxes_names:
                src_set = set(self.boxes[src]['outputs'].keys())
                dst_set = set(self.boxes[dst]['inputs'].keys())
                if src_set.intersection(dst_set):
                    self.dep_g.add_edge(src, dst)
        #nx_pydot.write_dot(self.dep_g, '/tmp/ddep.ddot')

    def _fill_boxes(self):
        """
        Fill input, output constraints and load them to the solver of
        each box.
        """
        for box_name in self.boxes:
            self.fill_boxes_input_constraints(box_name)
            # Load input constraints
            solver = self.boxes[box_name]['solver']
            solver.append(self.boxes[box_name]['box'].to_z3())
            for constraint in self.boxes[box_name]['input_constraints']:
                if constraint is None:
                    continue
                solver.append(constraint)
            # Load fixed input by the user
            print "Loading user provided input for box:", box_name
            solver.append(self.boxes[box_name]['fixed_inputs'])
            print "Loading user provided outputs for box:", box_name
            for constraint in self.boxes[box_name]['inputs']:
                if constraint in self.fixed_inputs:
                    solver.append(self.fixed_inputs[constraint])
            solver.append(self.boxes[box_name]['fixed_outputs'])
        print ''

    def evaluate_function(self, func, model):
        """
        Evaluate function over all possible values in the domain
        Z3 by default summarizes the functions, this force z3 to evaluate
        every single combination. However, this is very slow.
        """
        func_name = str(func)
        values = []

        def get_domain_values(domain):
            """Get all the possible value for a given function arg"""
            ret_val = None
            if domain == 'Node':
                ret_val = self.nodes
            elif domain == 'Network':
                ret_val = self.networks
            elif domain == 'Interface':
                ret_val = self.interfaces
            elif domain == 'AnnouncedNetwork':
                ret_val = self.announced_networks
            elif domain == 'NetworkOrAnnouncedNetwork':
                ret_val = self.announced_networks + self.networks
            elif domain == 'Protocol':
                ret_val = [get_string_const_val(p) for p in ['static', 'ospf', 'bgp']]
            elif domain == 'ASPath':
                ret_val = [get_string_const_val(p) for p in self.as_paths]
            elif domain == 'Int':
                ret_val = list(range(100))
            else:
                raise ValueError("Unknown domain '%s" % domain)
            return ret_val

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
                tmp = z3.Const('t%d' % i, self.node_sort)
                variables.append(tmp)
            elif t == 'Network':
                tmp = z3.Const('t%d' % i, self.network_sort)
                variables.append(tmp)
            elif t == 'Interface':
                tmp = z3.Const('t%d' % i, self.iface_sort)
                variables.append(tmp)
            elif t == 'AnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.network_sort)
                variables.append(tmp)
            elif t == 'NetworkOrAnnouncedNetwork':
                tmp = z3.Const('t%d' % i, self.network_sort)
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
        else_val = model[func].else_value()
        if z3.is_true(else_val) or z3.is_false(else_val):
            vals.append(str(else_val))
            return vals
        ret = self._get_function_vals(else_val.decl(), model)
        if ret:
            vals.extend(ret)
        return vals

    def print_box_results(self, box_name):
        print "For box", box_name
        model = self.boxes[box_name]['solver'].model()
        for name, func in self.boxes[box_name]['inputs'].iteritems():
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
        for name, func in self.boxes[box_name]['outputs'].iteritems():
            vals = self._get_function_vals(func, model)
            filterd_val = [val[:-1] for val in vals if z3.is_true(val[-1])]
            print "\tSynthesized output", name, filterd_val

    def get_ospf_constraints(self, ospf_route, ospf_route2, vals):
        ret = []
        t1, t2 = z3.Consts('t1 t2', z3.IntSort())
        v1, v2 = z3.Consts('v1 v2', self.vertex)

        for val in vals:
            if not isinstance(val, list):
                continue
            net, src, nxt = val[0], val[1], val[2]
            const = z3.And(
                z3.Exists(
                    [t1],
                    ospf_route(net, src, nxt, t1)),
                z3.Not(
                    z3.Exists(
                        [v1, t2],
                        z3.And(
                            ospf_route2(net, src, v1, t2),
                            v1 != v2,
                            t2 < t1))))
            ret.append(const)
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
            if box_name == 'ospf01':
                solver = z3.Solver()
                print 'partially evaluate the OSPF Datalog rules'
                translator = Translator(self.boxes[box_name]['file'], 1)
                ospf_costs = {}
                DEBUG_OSPF = False
                if DEBUG_OSPF:
                    ospf_routes = []
                    for ospf_route in self.boxes[box_name]['fixed_outputs']:
                        ospf_route = ospf_route.arg(0)
                        net = ospf_route.arg(0)
                        src = ospf_route.arg(1)
                        nxt = ospf_route.arg(2)
                        cost = ospf_route.arg(3)
                        ospf_routes.append([net, src, nxt, cost])
                    yes_func_vals['OSPFRoute'] = ospf_routes
                for out in yes_func_vals['OSPFRoute']:
                    if str(out) == 'False':
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
                ospf_reduced = tempfile.NamedTemporaryFile()
                print 'Writing OSPF partial evaluation rules to:', ospf_reduced.name
                ospf_reduced.write("""
                // ----------------------------- TYPES ----------------------------- //
                // Generic Vertex type
                Node(n) -> string(n).
                Network(n) -> string(n).
                Interface(n) -> string(n).
                ConnectedNodes(snode, siface, diface, dnode) ->
                Node(snode), Interface(siface), Interface(diface), Node(dnode).
                //EDB: SetOSPFEdgeCost, Node, Network, EdgePhy
                SetOSPFEdgeCost(src, dst, cost) -> Interface(src), Interface(dst), int(cost).
                //IDB: LinkOSPF, OSPFRoute
                OSPFRoute(net, src, next, cost) -> Network(net), Node(src), Node(next), int(cost).
                // ----------------------------- OSPF 1/2 ----------------------------- //
                """)
                for rule in translator.program.get_rules_for_predicate('OSPFRoute'):
                    if rule.head.name in [l.atom.name for l in rule.get_literals()]:
                        print rule
                        for net in ospf_costs.keys():
                            for src in ospf_costs[net].keys():
                                for nxt in ospf_costs[net][src].keys():
                                    src_nxt_link = \
                                    [link for link in self.connected_nodes if link[0] == src and link[3] == nxt][0]
                                    src_iface = src_nxt_link[1]
                                    nxt_iface = src_nxt_link[2]
                                    if nxt not in ospf_costs[net].keys():
                                        newRule = 'OSPFRoute_{}_{}_{}(cost) <- SetOSPFEdgeCost(src, nxt, cost), src="INTERFACE:{}", nxt="INTERFACE:{}", cost = {}.'.format(
                                            net, src, nxt, src_iface, nxt_iface, ospf_costs[net][src][nxt])
                                        print newRule
                                        ospf_reduced.write(newRule + '\n')
                                        newRule = 'OSPFRoute_{}_{}_{}(cost) -> int(cost).'.format(net, src, nxt)
                                        print newRule
                                        ospf_reduced.write(newRule + '\n')
                                    else:
                                        for next2 in ospf_costs[net][nxt].keys():
                                            newRule = 'OSPFRoute_{}_{}_{}(cost) <- SetOSPFEdgeCost(src, nxt, cost1), src="INTERFACE:{}", nxt="INTERFACE:{}", cost = cost1 + {}.'.format(
                                                net, src, nxt, src_iface, nxt_iface, ospf_costs[net][nxt][next2])
                                            print newRule
                                            ospf_reduced.write(newRule + '\n')
                                            newRule = 'OSPFRoute_{}_{}_{}(cost) -> int(cost).'.format(net, src, nxt)
                                            print newRule
                                            ospf_reduced.write(newRule + '\n')

                ospf_reduced.flush()
                with open(ospf_reduced.name) as f:
                    print "X" * 100
                    print f.read()
                    print "X" * 100
                newTranslator = Translator(ospf_reduced.name, self.unrolling_limit)
                newTranslator.STRING_TO_NODE = self.name_to_node
                newTranslator.STRING_TO_NET = self.name_to_network
                newTranslator.STRING_TO_INTERFACE = self.name_to_iface

                self.boxes[box_name]['solver'] = z3.Solver()
                self.boxes[box_name]['solver'].append(newTranslator.to_z3())

                for fix_output in yes_func_vals['OSPFRoute']:
                    if str(fix_output) == 'False':
                        continue
                    net = fix_output[0]
                    src = fix_output[1]
                    nxt = fix_output[2]
                    cost = fix_output[3]
                    c = newTranslator.predicates['OSPFRoute_{}_{}_{}'.format(net, src, nxt)](cost) == True
                    print c
                    self.boxes[box_name]['solver'].append(c)
                    t = z3.Const('cost', z3.IntSort())
                    c = z3.ForAll(
                        [t],
                        newTranslator.predicates[
                            'OSPFRoute_{}_{}_{}'.format(net, src, nxt)](t) == (t == cost))
                    print c
                    self.boxes[box_name]['solver'].append(c)

                for c in self.boxes[box_name]['input_constraints']:
                    if c is None: continue
                    self.boxes[box_name]['solver'].append(c)
                self.boxes[box_name]['solver'].append(self.boxes[box_name]['fixed_inputs'])
                for i in self.boxes[box_name]['inputs']:
                    if i in self.fixed_inputs:
                        # print "TO APPEND", box_name, self.fixed_inputs[i]
                        self.boxes[box_name]['solver'].append(self.fixed_inputs[i])
                self.boxes[box_name]['solver'].append(self.boxes[box_name]['fixed_outputs'])

            solver = self.boxes[box_name]['solver']
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
                    self.boxes[box_name]['outputs']['OSPFRoute_%d' % self.unrolling_limit],
                    self.boxes[box_name]['outputs']['OSPFRoute'], vals)
                solver.append(c)
            '''
            for func_name, func in self.boxes[box_name]['outputs'].iteritems():
                # Pre compute IGPRouteCost of OSPF
                if func_name == 'MinIGPBGPRoute' and 'BestOSPFRoute' in yes_func_vals and 'IGPRouteCost' in self.boxes[box_name]['inputs']:
                    IGPRouteCost = self.boxes[box_name]['inputs']['IGPRouteCost']
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

                    #v1, v2, v3 = z3.Consts('v1 v2 v3', self.vertex)
                    net1 = z3.Const('Net1', self.network_sort)
                    node1, node2 = z3.Consts('Node1 Node2', self.node_sort)
                    t1 = z3.Const('t1', z3.IntSort())
                    c = z3.ForAll(
                        [net1, node1, node2, t1],
                        IGPRouteCost(net1, node1, node2, t1) == z3.Or(
                            *[
                                z3.And(
                                    net1 == p[0],
                                    node1 == p[1],
                                    node2 == p[2],
                                    t1 == p[3]) for p in valid_igp]))
                    solver.append(c)
                orig_name = get_original_version(func_name)
                return_else = True
                if orig_name in ['BGPLocalPref', 'OSPFRoute']:
                    return_else = False
                if orig_name in yes_func_vals:
                    fed_output = self._process_vals(
                        func,
                        yes_func_vals[orig_name],
                        self.boxes[box_name]['outputs'],
                        return_else=return_else)
                    print "\tFeeding desired output", box_name, fed_output
                    #print fed_output
                    solver.append(fed_output)
            for t in no_box_vals[box_name]:
                #print "\tFeeding NOT desired input", box_name, t
                pass
            # Short cut inputs
            for func_name, func in self.boxes[box_name]['inputs'].iteritems():
                orig_name = get_original_version(func_name)
                return_else = True
                if orig_name in ['BGPLocalPref', 'OSPFRoute', 'nonMinOSPFRouteCost', 'nonMaxBGPLocalPref']:
                    return_else = False
                if orig_name in yes_func_vals:
                    fed_output = self._process_vals(
                        func,
                        yes_func_vals[orig_name],
                        self.boxes[box_name]['inputs'],
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
                for name, func in self.boxes[box_name]['inputs'].iteritems():
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
                #print self.boxes[box_name]['box'].to_z3()
                #print solver.to_smt2()
                #if box_index < len(self.boxes_names) - 1:
                #    self.print_box_results(self.boxes_names[box_index + 1])
                #return
                if box_index == len(self.boxes_names) - 1:
                    print solver.to_smt2()
                    print "FAILED!!!"
                    return
                solver.pop()
                box_index += 1
                #box_index = len(self.boxes_names) - 1
                #box_index = len(self.boxes_names) - 1
                box_name = self.boxes_names[box_index]
                print "!" * 20
                print "UNSAT going back to", box_index, box_name
                exit(-1)
                no_vals = []
                for func_name, func in self.boxes[box_name]['inputs'].iteritems():
                    orig_name = get_original_version(func_name)
                    if orig_name not in yes_func_vals:
                        continue
                    vals = yes_func_vals[orig_name]
                    if len(vals) == 0:
                        vals = ['False']
                    else:
                        vals.append('False')
                    vals = self._process_vals(func, vals, self.boxes[box_name]['inputs'], return_else=True)
                    no_vals.extend(vals)
                    del yes_func_vals[func_name]
                if box_name not in no_box_vals:
                    no_box_vals[box_name] = []
                no_box_vals[box_name].append(z3.Not(z3.And(*no_vals)))
        #for box_name in self.boxes_names:
        #    print self.boxes[box_name]['solver'].model()
        print "$"*40
        print "Final results..."
        for box_name in self.boxes_names:
            if box_name == 'OSPF_FIXED':
                print "For box", box_name
                syn = self.boxes['OSPF_FIXED']['ospf_fixed']
                for out in syn.get_output_configs():
                    print "\t", out
            else:
                self.print_box_results(box_name)
                #print self.boxes[box_name]['solver'].to_smt2()
                #print self.boxes[box_name]['solver'].model()

    def _common_datatypes(self):
        """Common data is_announced_network, is_protocol, is_as_path,
        is_as_path_length, constraints"""
        is_announced_network = z3.Function('is_announced_network',
                                           self.network_sort, z3.BoolSort())
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']
        is_protocol = z3.Function('is_protocol', string_sort, z3.BoolSort())
        is_as_path = z3.Function('is_as_path', string_sort, z3.BoolSort())
        is_as_path_length = z3.Function('is_as_path_length',
                                        string_sort, z3.IntSort(), z3.BoolSort())
        protocols = [get_string_const_val('static'),
                     get_string_const_val('ospf'),
                     get_string_const_val('bgp')]
        as_paths = [get_string_const_val(p) for p in self.as_paths]
        string_var = z3.Const('s1', string_sort)
        int_var = z3.Const('t1', z3.IntSort())
        self.connected_networks_f = z3.Function('ConnectedNetwork',
                                                self.node_sort, self.network_sort,
                                                z3.BoolSort())
        constraints = []
        # Mark externally learned networks
        for name, net in self.name_to_network.iteritems():
            if name in self.announced_network_names:
                constraints.append(is_announced_network(net) == True)
            else:
                constraints.append(is_announced_network(net) == False)

        # Constrain the protocols to only known ones
        constraints.append(
            z3.ForAll(
                [string_var],
                z3.Implies(
                    z3.Or([string_var == tmp for tmp in protocols]),
                    is_protocol(string_var) == True
                )))
        constraints.append(
            z3.ForAll(
                [string_var],
                z3.Implies(
                    z3.And(
                        [string_var != tmp for tmp in protocols]),
                    is_protocol(string_var) == False
                )))

        # Constrain AS Paths to only known ones
        if as_paths:
            constraints.append(
                z3.ForAll(
                    [string_var],
                    z3.Implies(
                        z3.Or([string_var == tmp for tmp in as_paths]),
                        is_as_path(string_var) == True
                    )))
            constraints.append(
                z3.ForAll(
                    [string_var],
                    z3.Implies(
                        z3.And(
                            [string_var != tmp for tmp in as_paths]),
                        is_as_path(string_var) == False
                    )))
        else:
            constraints.append(z3.ForAll([string_var],
                                         is_as_path(string_var) == False))

        if self.as_paths_length:
            constraints.append(
                z3.ForAll(
                    [string_var, int_var],
                    z3.Implies(
                        z3.Or(
                            [z3.And(string_var == p, int_var == l) for
                             p, l in self.as_paths_length.iteritems()]),
                        is_as_path_length(string_var, int_var) == True)))
            constraints.append(
                z3.ForAll(
                    [string_var],
                    z3.Implies(
                        z3.And(
                            [z3.Not(z3.And(string_var == p, int_var == l))
                             for p, l in self.as_paths_length.iteritems()]),
                        is_as_path_length(string_var, int_var) == False)))
        else:
            constraints.append(
                z3.ForAll([string_var, int_var],
                          is_as_path_length(string_var, int_var) == False))
        # Pair of directly connected routers
        self.directly_connected_nodes = z3.Function('DirectlyConnectedNodes',
                                                    self.node_sort, self.node_sort,
                                                    z3.BoolSort())

        return is_announced_network, is_protocol, is_as_path, is_as_path_length, constraints

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
        """
        Partially evaluate self.connected_networks_f(node, net) -> true if the
        network is attached to that given router
        """
        if self._tmp_connected_networks:
            return self._tmp_connected_networks
        constraints = []
        for src_name, src in self.name_to_node.iteritems():
            for dst_name, dst in self.name_to_network.iteritems():
                if (src_name, dst_name) in self.connected_networks:
                    constraints.append(self.connected_networks_f(src, dst) == True)
                else:
                    constraints.append(
                        self.connected_networks_f(src, dst) == False)
        self._tmp_connected_networks = constraints
        return self._tmp_connected_networks

    def fill_directly_connected_nodes(self):
        """
        Partially evaluate directly connected nodes
        self.directly_connected_nodes(node, node) -> true if there is
        an interfaces and link connecting them
        :return: constraints for the partial evaluation
        """
        # Check whether we already partially evaluated this value
        if self._tmp_dnodes:
            return self._tmp_dnodes
        constraints = []
        direct_nodes = []
        for sname in self.node_names:
            for siface in self.interface_names:
                for diface in self.interface_names:
                    for dname in self.node_names:
                        link = [sname, siface, diface, dname]
                        if link in self.connected_nodes:
                            direct_nodes.append((sname, dname))
        direct_nodes = list(set(direct_nodes))
        for sname, svar in self.name_to_node.iteritems():
            for dname, dvar in self.name_to_node.iteritems():
                if (sname, dname) in direct_nodes:
                    constraints.append(
                        self.directly_connected_nodes(svar, dvar) == True)
                else:
                    constraints.append(
                        self.directly_connected_nodes(svar, dvar) == False)
        self._tmp_dnodes = constraints
        return self._tmp_dnodes

    def generate_function_constraints(self, func):
        """
        Generate constraints to limit the search space of the function based
        on it's signature
        :param func: z3 function
        :return: constraints
        """
        (is_announced_network, is_protocol,
         is_as_path, is_as_path_length, _) = self._common_datatypes()
        string_sort = translator.LB_TYPE_TO_Z3_TYPE['string']
        func_name = str(func)
        assert func_name in FUNCS_SIG, \
            "The function '%s' has no signature defined" % func_name
        assert len(FUNCS_SIG[func_name]) == func.arity(), \
            "The function '%s' has different signature" % func_name
        variables = []
        checks = []
        # Iterate over the functions domain and generate constraints
        # to limit the search space of it (if necessary)
        for index, func_var in enumerate(FUNCS_SIG[func_name]):
            if func_var == 'Node':
                tmp = z3.Const('t%d' % index, self.node_sort)
                variables.append(tmp)
            elif func_var == 'Network':
                tmp = z3.Const('t%d' % index, self.network_sort)
                variables.append(tmp)
            elif func_var == 'Interface':
                tmp = z3.Const('t%d' % index, self.iface_sort)
                variables.append(tmp)
            elif func_var == 'AnnouncedNetwork':
                tmp = z3.Const('t%d' % index, self.network_sort)
                variables.append(tmp)
                checks.append(z3.Not(is_announced_network(tmp)))
            elif func_var == 'NetworkOrAnnouncedNetwork':
                tmp = z3.Const('t%d' % index, self.network_sort)
                variables.append(tmp)
            elif func_var == 'Int':
                tmp = z3.Const('t%d' % index, z3.IntSort())
                variables.append(tmp)
                if func_name.startswith('OSPFRoute'):
                    checks.append(z3.Not(z3.And(tmp <= MAX_OSPF_COST, tmp >= 0)))
                else:
                    checks.append(z3.Not(z3.And(tmp <= MAX_INT_VAL, tmp >= 0)))
            elif func_var == 'ASPathLength':
                tmp = z3.Const('t%d' % index, z3.IntSort())
                variables.append(tmp)
                if FUNCS_SIG[func_name][index - 1] == 'ASPath':
                    p = variables[-2]
                    checks.append(z3.Not(is_as_path_length(p, tmp)))
            elif func_var == 'ASPath':
                tmp = z3.Const('t%d' % index, string_sort)
                variables.append(tmp)
                checks.append(z3.Not(is_as_path(tmp)))
            elif func_var == 'Protocol':
                tmp = z3.Const('t%d' % index, string_sort)
                variables.append(tmp)
                checks.append(z3.Not(is_protocol(tmp)))
            else:
                err = "Unrecognized function %s domain '%s" % (func_name, func_var)
                raise ValueError(err)
        # Create the constraint
        constraint = [z3.ForAll(
            variables, z3.Not(z3.And(func(*variables), z3.Or(*checks))))]
        if func_name == 'BGPAnnouncement':
            constraint.append(
                z3.ForAll(
                    variables,
                    z3.Implies(
                        z3.Not(
                            z3.Or(
                                [z3.And([v == announcement[index]
                                         for index, v in enumerate(variables)])
                                 for announcement in self.bgp_annoucements])),
                        z3.Not(func(*variables)))))
        return constraint

    def fill_boxes_input_constraints(self, box_name):
        inputs = self.boxes[box_name]['inputs']
        outputs = self.boxes[box_name]['outputs']
        is_announced_network, is_protocol, is_as_path, is_as_path_length, constraints = self._common_datatypes()
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

        #v1, v2, v3, v4, v5, v6 = z3.Consts('v1 v2 v3 v4 v5 v6', self.vertex)

        net1, net2, net3 = z3.Consts('Net1 Net2 Net3', self.network_sort)
        node1, node2, node3, node4 = z3.Consts('Node1 Node2 Node3 Node4', self.node_sort)
        iface1, iface2, iface3 = z3.Consts('Iface1 Iface2 Iface3', self.iface_sort)

        int1, int2, int3, int4 = z3.Consts('t1 t2 t3 t4', z3.IntSort())
        str1, str2, str3 = z3.Consts('s1 s2 s3', string_sort)

        connected_networks_used = False
        directly_connected_nodes_used = False

        if IGPRouteCost is not None:
            # The cost of any not directly connected network is Zero
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(net1, node1, node2, int1),
                        self.connected_networks_f(node1, net1)),
                    int1 == 0))
            constraints.append(const)

            # The cost of any not directly connected network is more than zero
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(net1, node1, node2, int1),
                        z3.Not(self.connected_networks_f(node1, net1))),
                    int1 > 0))
            constraints.append(const)

        if MinIGPBGPRoute is not None:
            # HACK: FIXME we assume all the BGP routes has the the same preference
            # HACK: we need to propagate properly the ASPath Length from the input
            const = z3.ForAll(
                [node1, net1, net2, str1, int1, int2],
                z3.Implies(
                    MinIGPBGPRoute(node1, net1, net2, str1, int1, int2),
                    z3.And(int1 == 3, int2 == 6, is_announced_network(net2))))
            constraints.append(const)

        if nonMinIGPCost is not None and IGPRouteCost is not None:
            const = z3.ForAll(
                [net1, node1, node2, node3, int1, int1],
                z3.Implies(
                    z3.And(
                        IGPRouteCost(net1, node1, node2, int1),
                        IGPRouteCost(net1, node1, node3, int2),
                        int2 < int1),
                    nonMinIGPCost(node1, net1, int2)))
            constraints.append(const)

        if BGPAnnouncement is not None and BGPRoute is not None:
            const = z3.ForAll(
                [node1, net1, net2, str1, int1, int2],
                z3.Implies(
                    BGPRoute(node1, net1, net2, str1, int1, int2),
                    z3.Exists(
                        [node2],
                        z3.And(
                            BGPAnnouncement(node2, net1, net2, str1, int1, int2),
                            self.connected_networks_f(node2, net1)
                        ))))
            constraints.append(const)

        if BestOSPFRoute is not None:
            connected_networks_used = True
            directly_connected_nodes_used = True
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Not(
                        z3.Exists(
                            [node3, int2],
                            z3.And(
                                BestOSPFRoute(net1, node1, node3, int2),
                                int1 != int2)))))
            constraints.append(const)

            # Route cost should be larger than 0
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    int1 > 0))
            constraints.append(const)

            # Only one best BestOSPFRoute
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Not(
                        z3.Exists(
                            [node3, int2],
                            z3.And(
                                BestOSPFRoute(net1, node1, node3, int2),
                                node2 != node3)))))
            constraints.append(const)

            # If a route has BestOSPFRoute then the next hop should either have
            # a BestOSPFRoute for the given network or should be connected directly
            # to the given network
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Or(
                        self.connected_networks_f(node2, net1),
                        z3.Exists(
                           [node3, int2],
                            z3.And(
                                BestOSPFRoute(net1, node2, node3, int2),
                                int1 < int2,
                                node3 != node1)))))
            constraints.append(const)

            # Don't Forward directly connected networks
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Not(self.connected_networks_f(node1, net1))))
            constraints.append(const)

            # For a given router, BestOSPFRoute must forward any
            # given network to only one router
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Not(z3.Exists(
                        [node3, int2],
                        z3.And(
                            BestOSPFRoute(net1, node1, node3, int2),
                            node3 != node2)))))
            constraints.append(const)

            # OSPF must use the same next hop cost
            # if the two networks are on the same destination router
            const = z3.ForAll(
                [net1, node1, node2, net2, node3, int1, int2],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        BestOSPFRoute(net1, node1, node2, int1),
                        BestOSPFRoute(net2, node1, node3, int2),
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [node4],
                            z3.And(
                                self.connected_networks_f(node4, net1),
                                self.connected_networks_f(node4, net2),)),),
                    z3.And(node2 == node3, int1 == int2)))
            constraints.append(const)

            # Only route to directly connected nodes
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    self.directly_connected_nodes(node1, node2)))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    int1 <= 20))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, node2, net2, node3, int1, int2, int3],
                z3.Implies(
                    z3.And(
                        BestOSPFRoute(net1, node1, node2, int1),
                        self.connected_networks_f(node2, net1),
                        BestOSPFRoute(net2, node1, node2, int2),
                        BestOSPFRoute(net2, node2, node3, int3),
                        net2 != net1),
                    int1 == int2 - int3))
            constraints.append(const)

            # Ensure reasonable costs
            const = z3.ForAll(
                [net1, node1, node2, node3, net2, node4, int1, int2, int3, int4],
                z3.Implies(
                    z3.And(
                        BestOSPFRoute(net1, node1, node2, int1),
                        BestOSPFRoute(net1, node2, node3, int2),
                        BestOSPFRoute(net2, node1, node2, int3),
                        BestOSPFRoute(net2, node2, node4, int4),),
                    int1 - int2 == int3 - int4))
            constraints.append(const)

        if OSPFRoute is not None:
            connected_networks_used = True
            directly_connected_nodes_used = True

            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    OSPFRoute(net1, node1, node2, int1),
                    z3.Or(
                        self.connected_networks_f(node2, net1),
                        z3.Exists(
                            [node3, int2],
                            z3.And(
                                OSPFRoute(net1, node2, node3, int2),
                                int1 < int2,
                                node3 != node1)))))
            #constraints.append(const)

            const = z3.ForAll(
                [net1, node1, node2, node3, int1, int2],
                z3.Implies(
                    z3.And(
                        OSPFRoute(net1, node1, node2, int1),
                        OSPFRoute(net1, node1, node3, int2)),
                    int1 == int2))
            #constraints.append(c)

            # OSPF Route cost should be larger than 0
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    OSPFRoute(net1, node1, node2, int1),
                    int1 > 0))
            constraints.append(const)

            # OSPF must use the same next hop and cost
            # if the two networks are on the same destination router
            const = z3.ForAll(
                [net1, node1, node2, net2, node3, int1, int2],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        OSPFRoute(net1, node1, node2, int1),
                        OSPFRoute(net2, node1, node3, int2),
                        node2 == node3,
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [node4],
                            z3.And(
                                self.connected_networks_f(node4, net1),
                                self.connected_networks_f(node4, net2),)),),
                    z3.And(int1 == int2)))
            constraints.append(const)

            # Only route to directly connected nodes
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    OSPFRoute(net1, node1, node2, int1),
                    self.directly_connected_nodes(node1, node2)))
            constraints.append(const)

        #if SetStaticRouteCost is not None:
        #    const = datatype_route_cost(SetStaticRouteCost, is_network, is_node, self.vertex)
        #    constraints.append(const)

        if EdgePhy is not None:
            for src in self.network_graph.nodes():
                src_v = self.get_vertex(src)
                for dst in self.network_graph.nodes():
                    dst_v = self.get_vertex(dst)
                    if self.network_graph.has_edge(src, dst):
                        constraints.append(EdgePhy(src_v, dst_v) == True)
                    else:
                        constraints.append(EdgePhy(src_v, dst_v) == False)
            #const = z3.ForAll([v1, v2], z3.Implies(EdgePhy(v1, v2), EdgePhy(v2, v1)))
            constraints.append(const)

        if ConnectedNodes is not None:
            pairs = [
                [
                    self.name_to_node[p[0]],
                    self.name_to_iface[p[1]],
                    self.name_to_iface[p[2]],
                    self.name_to_node[p[3]],
                ] for p in self.connected_nodes]

            const = z3.ForAll(
                [node1, iface1, iface2, node2],
                ConnectedNodes(node1, iface1, iface2, node2) == z3.Or(
                    *[z3.And(
                        node1 == p[0], iface1 == p[1], iface2 == p[2], node2 == p[3])
                      for p in pairs]))
            constraints.append(const)

        if nonMinOSPFRouteCost is not None and OSPFRoute is not None:
            const = z3.ForAll(
                [net1, node1, int1],
                z3.Implies(
                    nonMinOSPFRouteCost(net1, node1, int1),
                    z3.Exists([node2], OSPFRoute(net1, node1, node2, int1))))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, int1],
                nonMinOSPFRouteCost(net1, node1, int1) == z3.Exists(
                    [node2, node3, int2],
                    z3.And(
                        OSPFRoute(net1, node1, node2, int1),
                        OSPFRoute(net1, node1, node3, int2),
                        int2 < int1)))
            constraints.append(const)

        if BestOSPFRoute is not None and nonMinOSPFRouteCost is not None:
            # Best route must be the min set
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    z3.Not(nonMinOSPFRouteCost(net1, node1, int1))))
            constraints.append(const)

        if minOSPFRouteCost is not None and BestOSPFRoute is not None:
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    BestOSPFRoute(net1, node1, node2, int1),
                    minOSPFRouteCost(net1, node1, int1)))
            constraints.append(const)

        if minOSPFRouteCost is not None and nonMinOSPFRouteCost is not None:
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    minOSPFRouteCost(net1, node1, int1),
                    z3.Not(nonMinOSPFRouteCost(net1, node1, int1))))
            constraints.append(const)

        if SetAdminDist is not None:
            # Set Admin Distance only once
            const = z3.ForAll(
                [node1, str1, int1],
                z3.Implies(
                    SetAdminDist(node1, str1, int1),
                    z3.Not(
                        z3.Exists(
                            [int2],
                            z3.And(
                                SetAdminDist(node1, str1, int2),
                                int1 != int2)))))
            constraints.append(const)

        if nonMinCostAD is not None:
            const = z3.ForAll(
                [net1, node1, str1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(net1, node1, int1),
                        is_announced_network(net1)
                    ), int1 == 2))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, str1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(net1, node1, int1),
                        z3.Not(is_announced_network(net1))
                    ), z3.Or(int1 == 1, int1 == 3)))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, str1],
                z3.Implies(
                    z3.And(
                        nonMinCostAD(net1, node1, int1),
                    ), int1 == 3))

            constraints.append(const)

        if nonMinCostAD is not None and SetAdminDist is not None and Route is not None:
            const = z3.ForAll(
                [net1, node1, node2, node3, str1, str2, int1],
                z3.And(
                    Route(net1, node1, node2, str1),
                    Route(net1, node1, node3, str2),
                    str1 != str2,
                    SetAdminDist(node1, str1, int1),
                    SetAdminDist(node1, str2, int2),
                    int1 < int2) == nonMinCostAD(net1, node1, int2))
            constraints.append(const)

        if nonMinCostAD is not None and SetAdminDist is not None and Route is not None:
            const = z3.ForAll(
                [net1, node1, int1],
                nonMinCostAD(net1, node1, int1) == z3.Exists(
                    [str1, str2, node2, int2],
                    z3.And(
                        SetAdminDist(node1, str1, int1),
                        Route(net1, node1, node2, str2),
                        SetAdminDist(node1, str2, int2),
                        int2 < int1)))
            constraints.append(const)

        if Fwd is not None:
            const = z3.ForAll(
                [net1, node1, node2, node3, str1, str2],
                z3.Implies(
                    z3.And(Fwd(net1, node1, node2, str1),
                           Fwd(net1, node1, node3, str2)),
                    z3.And(node3 == node2, str1 == str2)))
            constraints.append(const)

        if OSPFRoute is not None or BestOSPFRoute is not None:
            if OSPFRoute is not None:
                func = OSPFRoute
            elif BestOSPFRoute is not None:
                func = BestOSPFRoute
            # Block announced networks from being advertised over OSPF
            const = z3.ForAll(
                [net1, node1, node2, int1],
                z3.Implies(
                    is_announced_network(net1),
                    z3.Not(func(net1, node1, node2, int1))))
            constraints.append(const)

        if ConnectedBGPAnnouncement is not None:
            connected_networks_used = True
            const = z3.ForAll(
                [node1, net1, net2],
                z3.Implies(
                    ConnectedBGPAnnouncement(node1, net1, net2),
                    self.connected_networks_f(node1, net1)))
            constraints.append(const)

        if ConnectedBGPAnnouncement is not None and MaxBGPLocalPrefBGPRoute is not None:
            pass
            connected_networks_used = True
            const = z3.ForAll(
                [node1, net1, net2],
                ConnectedBGPAnnouncement(node1, net1, net2) == z3.Exists(
                    [str1, int1, int2],
                    z3.And(
                        MaxBGPLocalPrefBGPRoute(node1, net1, net2, str1, int1, int2),
                        self.connected_networks_f(node1, net1)
                    )
                )
            )
            #constraints.append(c)

        if nonMaxBGPLocalPref is not None and BGPLocalPref is not None:
            const = z3.ForAll(
                [node1, net2, net1, int1],
                nonMaxBGPLocalPref(net1, int1) == z3.And(
                    BGPLocalPref(node1, net2, net1, int1),
                    z3.Exists(
                        [node2, net3, int2],
                        z3.And(BGPLocalPref(node2, net3, net1, int2), int1 < int2))

                    ))
            constraints.append(const)

        if MaxBGPLocalPrefBGPRoute is not None and BGPLocalPref is not None:
            const = z3.ForAll(
                [node1, net1, net2, str1, int1, int2],
                z3.Implies(
                    MaxBGPLocalPrefBGPRoute(node1, net1, net2, str1, int1, int2),
                    z3.And(
                        BGPLocalPref(node1, net1, net2, int2),
                        z3.Not(
                            z3.Exists(
                                [node2, net3, int3],
                                z3.And(BGPLocalPref(node2, net3, net2, int3), int3 > int2))))))
            constraints.append(const)

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
            const = z3.ForAll(
                [node1, net1, net2, str1, int1, int2],
                z3.Implies(
                    MaxBGPLocalPrefBGPRoute(node1, net1, net2, str1, int1, int2),
                    z3.Not(
                        z3.Exists(
                            [node2, int3, int4],
                            z3.And(
                                MaxBGPLocalPrefBGPRoute(node2, net1, net2, str2, int3, int4),
                                int2 < int4
                            )
                        ))))
            constraints.append(const)

        if BGPRoute is not None and BGPLocalPref is not None:
            const = z3.ForAll(
                [node1, net1, net2, str1, int1, int2],
                z3.Implies(
                    BGPRoute(node1, net1, net2, str1, int1, int2),
                    z3.Exists([node2, int2], BGPLocalPref(node2, net1, net2, int2))))
            constraints.append(const)

        if SetNetwork is not None:
            const = z3.ForAll(
                [node1, node2, net1],
                z3.Implies(
                    z3.And(
                        SetNetwork(node1, net1) == True,
                        SetNetwork(node2, net1) == True),
                    node2 == node1))
            constraints.append(const)

        if SetInterface is not None:
            const = z3.ForAll(
                [node1, iface1],
                z3.Implies(
                    SetInterface(node1, iface1) == True,
                    z3.Not(
                        z3.Exists(
                            [node2],
                            z3.And(
                                node2 != node1,
                                z3.Or(SetInterface(node2, iface1)))))))
            constraints.append(const)

        if SetLink is not None:
            const = z3.ForAll(
                [iface1, iface2],
                z3.Not(
                    z3.And(
                        SetLink(iface1, iface2),
                        z3.Exists(
                            [iface3],
                            z3.And(
                                z3.Distinct(iface1, iface2, iface3),
                                z3.Or(SetLink(iface1, iface3),
                                      SetLink(iface3, iface1)))))))
            constraints.append(const)

        #if LinkOSPF is not None:
        #    const = z3.ForAll(
        #        [v1, v2, int1],
        #        z3.Implies(
        #            LinkOSPF(v1, v2, int1),
        #            z3.Exists(
        #                [v3, v4],
        #                z3.And(
        #                    EdgePhy(v1, v3),
        #                    EdgePhy(v3, v4),
        #                    SetOSPFEdgeCost(v3, v4, int1),
        #                    EdgePhy(v4, v2)))))
        #    constraints.append(const)

        #if SetOSPFEdgeCost is not None and EdgePhy is not None:
        #    const = z3.ForAll(
        #        [v1, v2, int1],
        #        z3.Implies(
        #            SetOSPFEdgeCost(v1, v2, int1),
        #            EdgePhy(v1, v2)))
        #    constraints.append(const)
        #    const = z3.ForAll(
        #        [v1, v2, int1],
        #        z3.Implies(
        #            SetOSPFEdgeCost(v1, v2, int1),
        #            z3.Not(z3.Exists([int2], z3.And(SetOSPFEdgeCost(v1, v2, int2), int1 != int2)))))
        #    constraints.append(const)

        if Route is not None:
            connected_networks_used = True
            # Cannot route back the same node
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    Route(net1, node1, node2, str1),
                    node1 != node2))
            constraints.append(const)

            # Externally learned prefixes, must be routed via BGP
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    z3.And(
                        Route(net1, node1, node2, str1),
                        is_announced_network(net1)
                    ), str1 == get_string_const_val('bgp')))
            constraints.append(const)

            # Internally learned prefixes cannot be routed over BGP
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    z3.And(
                        Route(net1, node1, node2, str1),
                        z3.Not(is_announced_network(net1))
                    ), str1 != get_string_const_val('bgp')))
            constraints.append(const)

            # Have continuous OSPFRoutes
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    z3.And(
                        Route(net1, node1, node2, str1),
                        str1 == get_string_const_val('ospf')),
                    z3.Exists(
                        [node3],
                        z3.Or(
                            z3.And(
                                Route(net1, node2, node3, str1),
                                node3 != node1
                            ),
                            self.connected_networks_f(node2, net1),
                        ))))
            # Long
            constraints.append(const)

            # Compute OSPF routes for all not directly connected networks
            const = z3.ForAll(
                [net1, node1],
                z3.Or(
                    self.connected_networks_f(node1, net1),
                    is_announced_network(net1),
                    z3.Exists(
                        [node2],
                        Route(net1, node1, node2, get_string_const_val('ospf')),
                    )))
            constraints.append(const)

            # There should be no more than one route for the same network,
            # the same protocol, the same router
            const = z3.ForAll(
                [net1, node1, node2, node3, str1],
                z3.Implies(
                    z3.And(
                        Route(net1, node1, node2, str1),
                        Route(net1, node1, node3, str1)),
                    node2 == node3))
            # Long
            constraints.append(const)

            # OSPF must use the same next hop if the two networks are on the same
            # destination router
            const = z3.ForAll(
                [net1, node1, node2, net2, node3, str1],
                z3.Implies(
                    z3.And(
                        # two Route entries on the same router
                        Route(net1, node1, node2, str1),
                        Route(net2, node1, node3, str1),
                        z3.Exists(
                            # The two networks are connected to the same dest router
                            [node4],
                            z3.And(
                                self.connected_networks_f(node4, net1),
                                self.connected_networks_f(node4, net2),
                            )),
                        str1 == get_string_const_val('ospf'),
                    ),
                    node2 == node3
                )
            )
            # Long
            constraints.append(const)

            directly_connected_nodes_used = True
            # Only route to directly connected nodes
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    Route(net1, node1, node2, str1),
                    self.directly_connected_nodes(node1, node2)))
            constraints.append(const)

        if Fwd is not None:
            connected_networks_used = True
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(Fwd(net1, node1, node2, str1), node1 != node2))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    z3.And(
                        Fwd(net1, node1, node2, str1),
                        is_announced_network(net1)
                    ), str1 == get_string_const_val('bgp')))
            constraints.append(const)

            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    z3.And(
                        Fwd(net1, node1, node2, str1),
                        z3.Not(is_announced_network(net1))
                    ), str1 != get_string_const_val('bgp')))
            constraints.append(const)

            directly_connected_nodes_used = True
            # Next hop can be only directly connected node
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    Fwd(net1, node1, node2, str1),
                    self.directly_connected_nodes(node1, node2)
                ))
            constraints.append(const)

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
            const = z3.ForAll(
                [net1, node1, node2, str1],
                z3.Implies(
                    Fwd(net1, node1, node2, str1),
                    z3.Not(
                        self.connected_networks_f(node1, net1))))
            constraints.append(const)

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
                    bgp_nets.append(self.name_to_network[net])
                else:
                    not_bgp_nets.append(self.name_to_network[net])
            #for net in not_bgp_nets:
            #    c = z3.Not(z3.Exists(
            #        [v1, v2, v3, s1, t1, t2],
            #        z3.And(
            #            MinAsPathBGPRoute(v1, v2, v3, s1, t1, t2),
            #            v2 == net)
            #    ))
            #    #constraints.append(c)

            #c = z3.ForAll(
            #    [v1, v2, v3, s1, t1, t2],
            #    z3.Implies(
            #        MinAsPathBGPRoute(v1, v2, v3, s1, t1, t2),
            #        z3.And(
            #            z3.Not(self.connected_networks_f(v2, v1)),
            #            z3.Or(*[v2 == net for net in bgp_nets]))
            #))
            ##constraints.append(c)

        #if OutgoingFwdInterface is not None and Fwd is not None and ConnectedNodes is not None:
        #    # Fwd entry must exists on the router to output the packet
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        OutgoingFwdInterface(v1, v2, v3) == z3.Exists(
        #            [v4, str1, v5],
        #            z3.And(
        #                Fwd(v1, v2, v4, str1),
        #                ConnectedNodes(v2, v3, v5, v4))))
        #    constraints.append(const)
#
        #if OutgoingFwdInterface is not None and Interface is not None:
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            OutgoingFwdInterface(v1, v2, v3),
        #            Interface(v3)))
        #    constraints.append(const)

        #if IncomingFwdInterface is not None and Fwd is not None and ConnectedNodes is not None:
        #    # Fwd entry must exists on a PREVIOUS router to output the packet
        #    # to this router
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        IncomingFwdInterface(v1, v2, v3) == z3.Exists(
        #            [v4, str1, v5],
        #            z3.And(Fwd(v1, v4, v3, str1),
        #                   ConnectedNodes(v4, v5, v2, v3))))
        #    constraints.append(const)

        #if OutgoingFwdInterface is not None:
        #    # Only one outgoing interface
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            OutgoingFwdInterface(v1, v2, v3),
        #            z3.Not(
        #                z3.Exists(
        #                    [v4, v5, v6],
        #                    z3.And(OutgoingFwdInterface(v4, v5, v6), v4 == v1, v5 == v2, v6 != v3)
        #                ))))
        #    constraints.append(const)

        #if OutgoingFwdInterface is not None and EdgePhy is not None:
        #    # Only have OutgoingFwdInterface through interfaces connected
        #    # directly to the router
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            OutgoingFwdInterface(v1, v2, v3),
        #            EdgePhy(v2, v3)))
        #    constraints.append(const)

        #if IncomingFwdInterface is not None and EdgePhy is not None:
        #    # Only have IncomingFwdInterface through interfaces connected
        #    # directly to the router
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            IncomingFwdInterface(v1, v2, v3),
        #            EdgePhy(v2, v3)))
        #    constraints.append(const)

        #if OutgoingFwdInterface is not None and IncomingFwdInterface is not None:
        #    # If an interface is marked as outgoing then it cannot be incomming as well
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            OutgoingFwdInterface(v1, v2, v3),
        #            z3.Not(IncomingFwdInterface(v1, v3, v2))))
        #    constraints.append(const)

        #    # If an interface is marked as incoming then it cannot be outgoing as well
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            IncomingFwdInterface(v1, v2, v3),
        #            z3.Not(OutgoingFwdInterface(v1, v3, v2))))
        #    constraints.append(const)

        #if OutgoingFwdInterface is not None and EdgePhy is not None and IncomingFwdInterface is not None:
        #    # If the router is not a terminating for the given network,
        #    # The must have IncomingFwdInterface
        #    # TODO(AH): NOT WORKING RIGHT NOW
        #    const = z3.ForAll(
        #        [v1, v2, v3],
        #        z3.Implies(
        #            z3.And(
        #                OutgoingFwdInterface(v1, v2, v3),
        #                z3.Not(EdgePhy(v1, v2))),
        #            z3.Exists(
        #                [v4, v5, v6],
        #                z3.And(IncomingFwdInterface(v4, v5, v6), v4 == v1, v6 == v2, v4 != v3))))
        #    #constraints.append(c)

        for name, func in self.boxes[box_name]['inputs'].iteritems():
            func_const = self.generate_function_constraints(func)
            #if name in ['MinAsPathBGPRoute']: continue
            constraints.append(func_const)
        for name, func in self.boxes[box_name]['outputs'].iteritems():
            func_const = self.generate_function_constraints(func)
            #print "OUTPUT", name, func_const
            #if name in ['OutgoingFwdInterface',
            #            'IncomingFwdInterface']: continue
            constraints.append(func_const)

        if directly_connected_nodes_used:
            constraints.extend(self.fill_directly_connected_nodes())
        if connected_networks_used:
            constraints.extend(self.fill_connected_networks_f())
        self.boxes[box_name]['input_constraints'] = constraints

    def read_init_inputs(self):
        """Add initial inputs as constraints to the solvers"""
        skipped = []
        self.bgp_annoucements = []
        for box_name in self.boxes_names:
            for op, name, args in self.init_inputs:
                func_true_vals = []
                parsed_args = []
                if name not in self.boxes[box_name]['inputs']:
                    skipped.append(name)
                    continue
                func = self.boxes[box_name]['inputs'][name]
                assert func.arity() == len(args), "%s %s" % (func, args)
                for i, arg in enumerate(args):
                    domain = str(func.domain(i))
                    if domain == 'NodeSort':
                        parsed_arg = self.name_to_node[arg]
                    elif domain == 'NetSort':
                        parsed_arg = self.name_to_network[arg]
                    elif domain == 'IfaceSort':
                        parsed_arg = self.name_to_iface[arg]
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
                self.boxes[box_name]['fixed_inputs'].append(f)
                #print "PROCESESS " * 50
                process = self._process_vals(func, func_true_vals + ['False'],
                                             self.boxes[box_name]['inputs'])
                #print process
                #self.boxes[box_name]['fixed_inputs'].extend(process)
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
                if name not in self.boxes[box_name]['outputs']:
                    skipped.append(name)
                    continue
                func = self.boxes[box_name]['outputs'][name]
                assert func.arity() == len(args), "%s %s" % (func, args)
                for i, arg in enumerate(args):
                    domain = str(func.domain(i))
                    if domain == 'NodeSort':
                        parsed_arg = self.name_to_node[arg]
                    elif domain == 'NetSort':
                        parsed_arg = self.name_to_network[arg]
                    elif domain == 'IfaceSort':
                        parsed_arg = self.name_to_iface[arg]
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
                else:
                    f = (func(parsed_args) == False)
                self.boxes[box_name]['fixed_outputs'].append(f)
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

    def get_name(self, vertex):
        """Takes a Z3 object and returns the corresponding name string """
        inv_map1 = {v: k for k, v in self.name_to_node.items()}
        inv_map2 = {v: k for k, v in self.name_to_network.items()}
        inv_map3 = {v: k for k, v in self.name_to_iface.items()}
        if vertex in inv_map1:
            return inv_map1[vertex]
        if vertex in inv_map2:
            return inv_map2[vertex]
        if vertex in inv_map3:
            return inv_map3[vertex]

    def _get_names(self):
        """
        Read the input files and extract all object names
        e.g., node names, network names, etc..
        :return: node_names, interface_names, network_names, announced_network_names
        """
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
                             'SetBGPLocalPref', 'SetAdminDist']:
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
                self.set_bgp_annoucement[edge].append(
                    (edge, net, ext, path, pathlength))
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

    def _create_vertices(self):
        # Extract all names from the input files
        (node_names, interface_names, network_names,
         announced_network_names) = self._get_names()
        self.node_names = node_names
        self.interface_names = interface_names
        self.network_names = network_names
        self.announced_network_names = announced_network_names
        nets = list(set(self.network_names + self.announced_network_names))
        (self.node_sort, self.nodes) = z3.EnumSort("NodeSort", self.node_names)
        (self.iface_sort, self.interfaces) = z3.EnumSort("IfaceSort", self.interface_names)
        (self.network_sort, self.networks) = z3.EnumSort("NetSort", nets)
        translator.LB_TYPE_TO_Z3_TYPE['Node'] = self.node_sort
        translator.LB_TYPE_TO_Z3_TYPE['Interface'] = self.iface_sort
        translator.LB_TYPE_TO_Z3_TYPE['Network'] = self.network_sort

        self.c = dict((str(v), v) for v in self.nodes)
        self.name_to_node = dict((str(v), v) for v in self.nodes)
        self.name_to_network = dict((str(v), v) for v in self.networks)
        self.name_to_iface = dict((str(v), v) for v in self.interfaces)
        translator.STRING_TO_NODE = self.name_to_node
        translator.STRING_TO_NET = self.name_to_network
        translator.STRING_TO_INTERFACE = self.name_to_iface
        self.announced_networks = [self.name_to_network[name] for name
                                   in self.announced_network_names]

    def construct_input_graph(self):
        """
        From the inputs constructs self.network_graph
        And fill self.connected_nodes with the tuples
        (src node, src iface, dst iface, dst node)
        that is used in partial eval
        :return: None
        """
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
        from synet.gen_configs import GNS3TopologyGen
        from synet.graph_util import get_bgp_attrs
        from synet.graph_util import SetAnnouncement
        from synet.graph_util import SetExternalPeer
        from synet.graph_util import add_input_filter
        from synet.graph_util import add_bgp_neighbor
        from synet.graph_util import add_ip_prefix_list
        from synet.graph_util import IPList


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
                        external_peers.append(
                            SetExternalPeer(net, peer_asnums[net], node))
                        if ext not in origins_asnums:
                            origins_asnums[ext] = nextorigin_asnum
                            nextorigin_asnum += 10
                        #def add_ip_prefix_list(g, node, iplist):
                        peername = 'AS%d' % peer_asnums[net]
                        attrs = {
                            VERTEX_TYPE: PEER_TYPE,
                            'bgp': {'asnum': peer_asnums[net],
                                    'neighbors': {}, 'announces': {}}
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

                        announcements.append(
                            SetAnnouncement(ext, net, node, origins_asnums[ext]))
                        peering_nets.append(ext)
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
                srouter = [i for i in self.network_graph.neighbors(src)
                           if is_router(self.network_graph, i)][0]
                drouter = [i for i in self.network_graph.neighbors(dst)
                           if is_router(self.network_graph, i)][0]
                g.add_edge(srouter, drouter, edge_type=INTERNAL_EDGE)
                if gen_ospf:
                    cost = self.ospf_costs.get((src, dst), None)
                    if cost is None:
                        cost = 65530
                    else:
                        cost = cost.as_long()
                    g[srouter][drouter]['ospf_cost'] = cost

        peering_nets = list(set(peering_nets))
        print "PEERINT NETS", peering_nets
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
