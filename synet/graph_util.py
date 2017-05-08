#!/usr/bin/env python
"""
Various functions to help manipulate the network graph
"""

from collections import namedtuple

from common import VERTEX_TYPE, PEER_TYPE, EDGE_TYPE, ANNOUNCEMENT_EDGE



__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"


IPList = namedtuple('IPList', ['Name', 'Prefixes', 'Action'])

# The Prefix being announced, and the next Hop IP address
SetAnnouncement = namedtuple('BGPAnnouncement', ['Prefix', 'NextHopIP', 'Router', 'OriginAS'])

# Declare our external peers
# The nextHopIp and the remote AS number of the external peer and the local router
# peering with that peer
SetExternalPeer = namedtuple('SetExternalPeer', ['NextHopIP', 'RemoteAS', 'Router'])

# Create a Tag for a set of IP prefixes
TagPrefixes = namedtuple('TagPrefixes', ['Tag', 'Prefixes'])

# Create a Tag for routes announced by certain peers
TagIncomingRoutes = namedtuple('TagEdgeRouters', ['Tag', 'NextHopIPs'])

# User input for polcies to exit the network from a certain Next Hop IPs
iBGPExists = namedtuple('iBGPExists', ['Match', 'LocalRouters', 'NextHops'])

# User input for polcies to block traffic from existing the network
# from a certain Next Hop IPs
iBGPNotExists = namedtuple('iBGPNotExists', ['Match', 'LocalRouters', 'NextHopIPs'])

# Export certain prefixes through given routers
BGPExport = namedtuple('BGPExport', ['Match', 'LocalRouters', 'NextHopIPs'])

# Don't Export certain prefixes through given routers
BGPNotExport = namedtuple('BGPNotExport', ['Match', 'LocalRouters', 'NextHopIPs'])

# Config to set Import LocalPref
SetImportLocalPref = namedtuple('SetImportLocalPref', ['Router', 'Match', 'LocalPref'])

# Don't import certain tags.
SetImportDeny = namedtuple('SetImportDeny', ['Match', 'Router'])

# Dont export certain tags
SetExportDeny = namedtuple('SetExportDeny', ['Match', 'Router'])

# Export certain tags
SetExport = namedtuple('SetExport', ['Match', 'Router'])

# Config local BGP
SetLocalASNum = namedtuple('SetLocalASNum', ['ASNum'])

# Config Route Map, it consistes of one or more RouteMapLine
SetRouteMap = namedtuple('SetRouteMapFilter', ['Name', 'Lines'])

# Route Map Line
SetRouteMapLine = namedtuple('RouteMapLine', ['Access', 'LineNo', 'Match', 'Action'])


class CommunityList(object):
    """A Conjunction of Tags"""
    def __init__(self, tags, action='permit'):
        for tag in tags:
            assert isinstance(tag, Tag)
        assert action in ['permit', 'deny']
        self.tags = tags
        self.action = action

    @property
    def name(self):
        return "CommList_And_%s" % '_'.join([t.name for t in self.tags])

    def to_list(self):
        name = self.name
        action = self.action
        l = ' '.join([str(t.to_community()) for t in self.tags])
        return 'ip community-list standard %s %s %s' % (name, action, l)



class Match(object):
    """Match on one or more tags"""
    def to_match(self):
        raise NotImplemented()


class Tag(Match):
    """Represents a community tag on BGP advertisement"""
    next_community = 1000
    TAGS = {}  # Set of local known tags to avoid duplicates
    LOCALAS = None  # Set Local ASNum to have tags generated as ASNUM:TagNo

    def __init__(self, name):
        """Give the community a string name"""
        assert name not in Tag.TAGS
        self.name = name
        Tag.TAGS[self.name] = self
        self.tag_community = None

    def to_community(self):
        """Community values are actually integers"""
        # No community for any tag
        if self.name == '*':
            return None
        if not self.tag_community:
            self.tag_community = Tag.next_community
            Tag.next_community += 1
        if not Tag.LOCALAS:
            return "%d" % (self.tag_community)
        else:
            return "%d:%d" % (self.LOCALAS, self.tag_community)

    def to_match(self):
        """Returns a match for the route map"""
        # No match for any tag
        if self.name == '*':
            return None
        return CommunityList([self])

    def __eq__(self, other):
        return self.name == other.name and self.to_community() == other.to_community()

    def __repr__(self):
        return "%s(%s)" % (self.name, str(self.to_community()))


class AndTag(Match):
    """Match on multiple tags"""

    def __init__(self, *tags):
        for tag in tags:
            assert isinstance(tag, (Tag, AndTag))
        all_tags = []
        # Unroll nested AndTags
        for tag in tags:
            if isinstance(tag, AndTag):
                all_tags.extend(tag.tags)
            elif tag.name == '*':
                continue
            else:
                all_tags.append(tag)
        self.tags = all_tags

    @property
    def name(self):
        """Human readable name, and used to generate route maps"""
        return "And_%s" % '_'.join([t.name for t in self.tags])

    def to_match(self, access='permit'):
        """Returns a match for the route map"""
        return CommunityList(self.tags, access)

    def __eq__(self, other):
        return  set(self.tags) == set(other.tags)

    def __repr__(self):
        return "And(%s)" % [str(repr(t)) for t in self.tags]

    def __str__(self):
        return "And_%s" % '_'.join([str(repr(t)) for t in self.tags])


AnyTag = Tag('*')


def get_bgp_attrs(g, node):
    """Return a dict of all BGP related attrs given to a node"""
    if 'bgp' not in g.node[node]:
       g.node[node]['bgp'] = {'asnum': None, 'neighbors': {}, 'announces': {}}
    return g.node[node]['bgp']


def get_bgp_neighbors(g, node):
    """Get A dictionary of BGP peers"""
    return get_bgp_attrs(g, node)['neighbors']


def add_bgp_neighbor(g, routerA, routerB):
    """Add BGP peer"""
    neighborsA = get_bgp_neighbors(g, routerA)
    neighborsB = get_bgp_neighbors(g, routerB)
    asnumA = get_bgp_asnum(g, routerA)
    asnumB = get_bgp_asnum(g, routerB)
    if routerB not in neighborsA:
        neighborsA[routerB] = {'remoteas': asnumB}
    if routerA not in neighborsB:
        neighborsB[routerA] = {'remoteas': asnumA}


def get_bgp_asnum(g, node):
    """Get the AS number of a given router"""
    return get_bgp_attrs(g, node)['asnum']


def get_bgp_neighbor_remoteas(g, node, neighbor):
    """Get the AS number of a BGP peer"""
    neighbors = get_bgp_neighbors(g, node)
    return neighbors[neighbor]['remoteas']


def get_bgp_announces(g, node):
    """Get a dictionary of BGP announced netwrok by a given router"""
    return get_bgp_attrs(g, node)['announces']


def add_bgp_announces(g, node, name, net=None, tags=[]):
    """Add a network to be BGP announced by a router"""
    announces = get_bgp_announces(g, node)
    if name not in announces:
        announces[name] = {'tags': [], 'net': net}
    if tags:
        announces[name]['tags'] = tags
    if net:
        announces[name]['net'] = net

def add_bgp_announces_tag(g, node, name, tag):
    print "ADDED tag", name, tag
    add_bgp_announces(g, node, name)
    announces = get_bgp_announces(g, node)
    announces[name]['tags'].append(tag)


def add_bgp_external_peer(g, node, remoteas, nexthop):
    """Add a node to the graph of a external peer"""
    peer = "AS%s" % remoteas
    if not g.has_node(peer):
        attrs = {
            VERTEX_TYPE: PEER_TYPE,
            'bgp': {'asnum': remoteas, 'neighbors': {}, 'announces': {}}
        }
        g.add_node(peer, **attrs)
    g.add_edge(node, peer, **{EDGE_TYPE: ANNOUNCEMENT_EDGE, 'nexthop': nexthop})
    g.add_edge(peer, node, **{EDGE_TYPE: ANNOUNCEMENT_EDGE})
    # Define BGP peering
    add_bgp_neighbor(g, node, peer)


def get_neighbor_by_nexthop(g, node, nexthop):
    """Get the router who is a neighbor with a given nexthop"""
    neighbors = get_bgp_neighbors(g, node)
    for n, attrs in neighbors.iteritems():
        if g[node][n].get('nexthop', None) == nexthop:
            return n


def add_bgp_neighbor_import_local_pref(g, node, neighbor, localpref):
    prefs = get_bgp_neighbor_import_local_prefs(g, node, neighbor)
    prefs.append(localpref)


def get_bgp_neighbor_import_local_prefs(g, node, neighbor):
    attrs = get_bgp_neighbors(g, node)[neighbor]
    if 'ImportLocalPref' not in attrs:
        attrs['ImportLocalPref'] = []
    return attrs['ImportLocalPref']


def add_import_tag_to_node(g, node, neighbor, tag):
    """Tag incoming announcements"""
    attrs = get_bgp_neighbors(g, node)[neighbor]
    if 'ImportTags' not in attrs:
        attrs['ImportTags'] = {}
    assert tag.Tag not in attrs['ImportTags'], tag.Tag
    attrs['ImportTags'][tag.Tag] = tag


def get_node_import_tags(g, node, neighbor):
    """Get all incoming announcements Tags"""
    attrs = get_bgp_neighbors(g, node)[neighbor]
    if 'ImportTags' not in attrs:
        attrs['ImportTags'] = {}
    return attrs['ImportTags']


def add_ip_prefix_list(g, node, iplist):
    assert isinstance(iplist, IPList)
    name = iplist.Name
    attrs = get_ip_prefix_lists(g, node)
    assert name not in attrs, "List '%s' already defined" % name
    attrs[name] = iplist

def get_ip_prefix_lists(g, node):
    attrs = g.node[node]
    if 'ip_prefix_list' not in attrs:
        attrs['ip_prefix_list'] = {}
    return attrs['ip_prefix_list']


def add_input_filter(g, node, neighbor, access, match, action, lineno=None):
    inmap = get_input_filters(g, node, neighbor)
    if lineno is None:
        if not inmap:
            lineno = 10
        else:
            lineno = inmap[-1].LineNo + 10
    line = SetRouteMapLine(access, lineno, match, action)
    inmap.append(line)


def get_input_filters(g, node, neighbor):
    neighbors = get_bgp_neighbors(g, node)
    if 'InputMaps' not in neighbors[neighbor]:
        neighbors[neighbor]['InputMaps'] = []
    inmap = neighbors[neighbor]['InputMaps']
    return inmap


def add_output_filter(g, node, neighbor, access, match, action, lineno=None):
    outputmap = get_output_filters(g, node, neighbor)
    if lineno is None:
        if not outputmap:
            lineno = 10
        else:
            lineno = outputmap[-1].LineNo + 10
    line = SetRouteMapLine(access, lineno, match, action)
    outputmap.append(line)


def get_output_filters(g, node, neighbor):
    neighbors = get_bgp_neighbors(g, node)
    if 'OutputMaps' not in neighbors[neighbor]:
        neighbors[neighbor]['OutputMaps'] = []
    return neighbors[neighbor]['OutputMaps']


def add_community_list(g, node, community_list):
    assert isinstance(community_list, CommunityList)
    clists = get_community_lists(g, node)
    if community_list.name not in clists:
        clists[community_list.name] = community_list


def get_community_lists(g, node):
    attrs = get_bgp_attrs(g, node)
    if 'community_lists' not in attrs:
        attrs['community_lists'] = {}
    return attrs['community_lists']


def add_bgp_neighbor_export_deny(g, node, neighbor, deny):
    prefs = get_bgp_neighbor_export_deny(g, node, neighbor)
    prefs.append(deny)


def get_bgp_neighbor_export_deny(g, node, neighbor):
    attrs = get_bgp_neighbors(g, node)[neighbor]
    if 'ExportDeny' not in attrs:
        attrs['ExportDeny'] = []
    return attrs['ExportDeny']


def add_bgp_neighbor_export(g, node, neighbor, export):
    prefs = get_bgp_neighbor_export(g, node, neighbor)
    prefs.append(export)


def get_bgp_neighbor_export(g, node, neighbor):
    attrs = get_bgp_neighbors(g, node)[neighbor]
    if 'Export' not in attrs:
        attrs['Export'] = []
    return attrs['Export']

