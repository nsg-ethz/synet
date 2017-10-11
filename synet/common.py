"""
Common functions for synthesis
"""


import z3
from enum import Enum
from collections import namedtuple
from networkx.drawing import nx_pydot


# Keys for annotations used in nx graphs
NODE_TYPE = '"node"'
EXTERNAL_NODE_TYPE = '"external_node"'
INTERFACE_TYPE = '"interface"'
NETWORK_TYPE = '"network"'
INTERNAL_EDGE = '"internal"'
LINK_EDGE = '"link"'
StaticRoutes = 'StaticRoutes'
OSPFRoutes = 'OSPFRoutes'
OSPFBestRoutes = 'OSPFBestRoutes'
OSPFBestRoutesCost = 'OSPFBestRoutesCost'
FwdRoutes = 'FwdRoutes'
VERTEX_TYPE = 'vertex_type'
EDGE_TYPE = 'edge_type'
ANNOUNCEMENT_EDGE='annoucement_edge'
ANNOUNCED_NETWORK='announced_network'
PEER_TYPE="peer"
ORIGIN_TYPE="as_origin"
AS_NUM = 'AS'


class PathProtocols(Enum):
    """List all protocols"""
    Forwarding = 1
    Static = 2
    OSPF = 3
    BGP = 4
    ASPATH = 5


# Define requirements signature.
(z3_proto, all_protocols) = z3.EnumSort('Protocols', ['Static',  'OSPF', 'BGP'])
z3_static, z3_ospf, z3_bgp = all_protocols

PathReq = namedtuple('PathRequirement', ['protocol', 'dst_net', 'path', 'cost'])
PathOrderReq = namedtuple('PathOrderRequirement', ['protocol', 'dst_net', 'paths', 'cost'])
NotPathReq = namedtuple('NotPathRequirement', ['protocol', 'dst_net', 'path'])
ReachabilityReq = namedtuple('ReachabilityRequirement',
                             ['protocol', 'dst_net', 'src', 'dst',
                              'min_k', 'max_k'])
NotReachabilityReq = namedtuple('NotReachabilityRequirement',
                                ['protocol', 'dst_net', 'src', 'dst',
                                 'min_k', 'max_k'])
WayPointReq = namedtuple('WayPointRequirement',
                         ['protocol', 'dst_net', 'vertices'])
NotWayPointReq = namedtuple('NotWayPointRequirement',
                            ['protocol', 'dst_net', 'vertices'])


# Define common functions
# Data types
def z3_is_node(vertex):
    """Returns True if the vertex is of type node (aka router)"""
    return z3.Function('IsNode', vertex, z3.BoolSort())


def z3_is_interface(vertex):
    """Returns True if the vertex is of type interface"""
    return z3.Function('IsInterface', vertex, z3.BoolSort())


def z3_is_network(vertex):
    """Returns True if the vertex is of type network"""
    return z3.Function('IsNetwork', vertex, z3.BoolSort())

def z3_is_bgp_node(vertex):
    """Returns True if the vertex is configured to be BGP router"""
    return z3.Function('IsBGPNode', vertex, z3.BoolSort())


# Simulating input configurations
def z3_set_node(vertex):
    """Add a node"""
    return z3.Function('SetNode', vertex, z3.BoolSort())


def z3_set_interface(vertex):
    """Assign an interface to a router"""
    return z3.Function('SetInterface', vertex, vertex, z3.BoolSort())


def z3_set_network(vertex):
    """Add a network"""
    return z3.Function('SetNetwork', vertex, vertex, z3.BoolSort())


def z3_set_link(vertex):
    """Creates a physical ethernet link between two interfaces"""
    return z3.Function('SetLink', vertex, vertex, z3.BoolSort())

def z3_edge(vertex):
    """True is an edge exists between two vertices"""
    return z3.Function('Edge', vertex, vertex, z3.BoolSort())


def datatypes_unique(common_type, type_checkers=[]):
    ret = []
    v = z3.Const('v', common_type)
    for check1 in type_checkers:
        for check2 in type_checkers:
            if str(check1) == str(check2): continue
            ret.append(
                z3.ForAll([v], z3.Not(z3.And(check1(v), check2(v)))))
    return ret


def datatype_route(route, is_network, is_node, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3))))))
    c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3), v2 == v3)))
    return [c, c2]


def datatype_route_protocol(route, is_network, is_node, is_protocol, protocol_type, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', protocol_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3)),
                    z3.Not(is_protocol(v4))))))
    c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3, v4), v2 == v3)))
    return [c, c2]


def datatype_route_cost(route, is_network, is_node, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', z3.IntSort())
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3))))))
    #c2 = z3.ForAll([v1, v2, v3], z3.Not(z3.And(route(v1, v2, v3, v4), v2 == v3)))
    c2 = z3.ForAll([v1, v2, v3, v4], z3.Implies(v2 == v3, z3.Not(route(v1, v2, v3, v4))))
    return [c, c2]


def datatype_route_bgp(route, is_network, is_node, is_as_path_length, as_path_type, vertex_type):
    """
    Constrain route data type
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    v4 = z3.Const('v4', as_path_type)
    v5 = z3.Const('v5', z3.IntSort())
    v6 = z3.Const('v6', z3.IntSort())
    c = z3.ForAll(
        [v1, v2, v3, v4, v5, v6],
        z3.Not(
            z3.And(
                route(v1, v2, v3, v4, v5, v6),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_node(v3)),
                    z3.Not(is_as_path_length(v4, v5))))))
    c2 = z3.ForAll([v1, v2, v3, v4, v5, v6], z3.Not(z3.And(route(v1, v2, v3, v4, v5, v6), v2 == v3)))
    return [c2]
    return [c, c2]


def datatype_network_node_interface(func, is_network, is_node, is_interface, vertex_type):
    """
    Constrain a function  with (network, node, interface) signature
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                func(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_node(v2)),
                    z3.Not(is_interface(v3))))))
    return [c]


def datatype_network_interface_node(func, is_network, is_node, is_interface, vertex_type):
    """
    Constrain a function  with (node, interface) signature
    """
    v1, v2, v3 = z3.Consts('v1 v2 v3', vertex_type)
    c = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                func(v1, v2, v3),
                z3.Or(
                    z3.Not(is_network(v1)),
                    z3.Not(is_interface(v2)),
                    z3.Not(is_node(v3))))))
    return [c]


def z3_interface_links(vertex, is_interface, edge, bidir=True):
    v1, v2, v3, v4 = z3.Consts('v1 v2 v3 v4', vertex)
    # Make sure we don't have more than one outgoing link from each interface
    # to another interface
    outgoing = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                is_interface(v1),
                is_interface(v2),
                is_interface(v3),
                z3.Distinct(v1, v2, v3),
                edge(v1, v2),
                edge(v1, v3)
            )))

    # Make sure we don't have more than one incoming link from each interface
    # to another interface
    incoming = z3.ForAll(
        [v1, v2, v3],
        z3.Not(
            z3.And(
                is_interface(v1),
                is_interface(v2),
                is_interface(v3),
                z3.Distinct(v1, v2, v3),
                edge(v2, v1),
                edge(v3, v1)
            )))

    # We're modeling an ethernet network, so we get the second link for free
    if bidir:
        bidir_c = z3.ForAll(
            [v1, v2],
            z3.Implies(
                z3.And(
                    is_interface(v1),
                    is_interface(v2),
                    edge(v1, v2)
                ),
                edge(v2, v1)
            ))
    constraints = [outgoing, incoming]
    if bidir:
        constraints.append(bidir_c)
    return constraints



def draw(g, out):
    """
    Write the graph in a dot file.

    This function creates a shallow copy of the graph and removes
    all unnecessary attributes for drawing, otherwise dotx wont be able to
    visualize the graph.
    """
    def _allowed_attrs(attrs):
        new_attrs = {}
        if attrs.get('shape', None):
            new_attrs['shape'] = attrs['shape']
        if attrs.get('style', None):
            new_attrs['style'] = attrs['style']
        if not attrs.get('cost', None) is None:
            new_attrs['label'] = attrs['cost']
        return new_attrs
    clean_g = g.copy()
    for n, attrs in clean_g.nodes(True):
        clean_g.node[n] = _allowed_attrs(attrs)
    for src, dst, attrs in clean_g.edges(data=True):
        clean_g.edge[src][dst] = _allowed_attrs(attrs)
    nx_pydot.write_dot(clean_g, out)
