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
