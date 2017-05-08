import ipaddress
from itertools import count
import shutil
import os


from common import NODE_TYPE, NETWORK_TYPE, VERTEX_TYPE, PEER_TYPE
from common import ORIGIN_TYPE, EDGE_TYPE, ANNOUNCEMENT_EDGE

#from ibgp_tags import *
from graph_util import *


def IP2Int(ip):
    o = map(int, ip.split('.'))
    res = (16777216 * o[0]) + (65536 * o[1]) + (256 * o[2]) + o[3]
    return res


"""
BGP config
self.g.node[node] = {
'bgp': {
        'asnum': 'Router's AS Number',
        'announces': 'List of announcements',
        'neighbors': {
                'neighbor router': {
                    'remoteas': 'remote as number',
                }
            }
    }
}
"""


class ConfigBGPNodes(object):
    def __init__(self, g, external_peers, announcements, network_addr_map):
        self.g = g
        self.external_peers = external_peers
        self.announcements = announcements
        self.network_addr_map = network_addr_map
        self._nexthop_to_router = {}

    def generate_peer_routers(self):
        """Generate a node of each peer"""
        # Group peers by AS Number
        peers = {}
        for peer in self.external_peers:
            remoteas = peer.RemoteAS
            if remoteas not in peers:
                peers[remoteas] = []
            peers[remoteas].append(peer)

        # Add one router for each AS
        for remoteas, vals in peers.iteritems():
            node = "AS%s" % remoteas
            attrs = {
                VERTEX_TYPE: PEER_TYPE,
                'bgp': {'asnum': remoteas, 'neighbors': {}, 'announces': {}}
            }
            self.g.add_node(node, **attrs)
            for c in vals:
                net = ipaddress.ip_network(self.network_addr_map[c.NextHopIP])
                self._nexthop_to_router[c.NextHopIP] = node
                a1, a2 = [i for i in net][:2]
                add_bgp_neighbor(self.g, node, c.Router)
                self.g.add_edge(node, c.Router, addr=a1, net=net, **{EDGE_TYPE: ANNOUNCEMENT_EDGE})
                self.g.add_edge(c.Router, node, addr=a2, net=net, **{EDGE_TYPE: ANNOUNCEMENT_EDGE})
                print "Adding input filter", c.Router, node
                #add_input_filter(self.g, c.Router, node, access='permit', match=None,
                #                 action='set local-preference 200')

    def generate_annoucement_routers(self):
        """
        For each AS that announces one or more prefixes create a router
        """
        # Group announcements by AS Number
        asnum_map = {}
        for announcement in self.announcements:
            originas = announcement.OriginAS
            if originas not in asnum_map:
                asnum_map[originas] = []
            asnum_map[originas].append(announcement)
        # For each AS add a node to the graph
        for asnum, anns in asnum_map.iteritems():
            node = 'AS%s' % asnum
            announces = {}
            for ann in anns:
                announces[ann.Prefix] = {
                    'rmap': None,
                    'net': ipaddress.ip_network(self.network_addr_map[ann.Prefix])
                }
            attrs = {
                VERTEX_TYPE: ORIGIN_TYPE,
                'bgp': {'asnum': asnum, 'neighbors': {}, 'announces': announces}
            }
            self.g.add_node(node, **attrs)

            for ann in anns:
                nexthop = ann.NextHopIP
                router = self._nexthop_to_router[nexthop]
                prefix = ann.Prefix
                if self.g.has_edge(node, router): continue
                add_bgp_neighbor(self.g, node, router)
                self.g.add_edge(node, router,
                                **{EDGE_TYPE: ANNOUNCEMENT_EDGE})
                self.g.add_edge(router, node,
                                **{EDGE_TYPE: ANNOUNCEMENT_EDGE})

                self.g.add_node(prefix, **{VERTEX_TYPE: NETWORK_TYPE})
                self.g.add_edge(prefix, node, **{EDGE_TYPE: NETWORK_TYPE})
                self.g.add_edge(node, prefix, **{EDGE_TYPE: NETWORK_TYPE})


class GNS3TopologyGen(object):
    def __init__(self, g,
                 network_addr_map={},
                 external_peers=[],
                 bgp_announcements=[],
                 gen_ospf=True,
                 gen_bgp=True,
                 console_start_port=2501,
                 dynampisaddr='127.0.0.1:7200',
                 workingdir='/home/ahassany/tt',
                 idlepc='0x631868a4',
                 outdir='out',
                 iosimage='/home/ahassany/GNS3/images/IOS/c7200-advipservicesk9-mz.152-4.S5.image'):
        self.g = g
        self.external_peers = external_peers
        self.announcements = bgp_announcements
        self.gen_ospf = gen_ospf
        self.gen_bgp = gen_bgp
        self.local_dynampis = dynampisaddr
        self.workingdir = workingdir
        self.router_model = '7200'
        self.outdir = outdir
        self.router_info = {
            'image': iosimage,
            'npe': 'npe-400',
            'ram':'256',
            'nvram': '50',
            'idlepc': idlepc,
            'idlemax': '500',
        }
        self.next_console = count(console_start_port)
        self.network_addr_map = network_addr_map
        self._nexthop_to_router = {}

        if self.gen_bgp:
            for src in self.local_routers_iter():
                for dst in self.local_routers_iter():
                    if src == dst: continue
                    add_bgp_neighbor(g, src, dst)
            self.bgp_config = ConfigBGPNodes(g, self.external_peers,
                                             self.announcements,
                                             self.network_addr_map)
            self.bgp_config.generate_peer_routers()
            self.bgp_config.generate_annoucement_routers()

        # First annotate the nodes with the necessary information
        for n in sorted(self.g.nodes()):
            if self.is_router(n):
                self.annotate_node(n)
            elif self.is_network(n):
                self.annotate_network(n)

        self.assign_ip_addresses()
        self.assign_loopback()

        shutil.rmtree(self.outdir, True)
        self.scriptsdir = '%s/scripts' % self.outdir
        self.configsdir = '%s/configs' % self.outdir
        os.mkdir(self.outdir)
        os.mkdir(self.scriptsdir)
        os.mkdir(self.configsdir)

        # Generate Topology file
        topo = self.generate_topo()
        with open('%s/topo.ini' % self.outdir, 'w') as f:
            f.write(topo)
        # Generate config file for each router
        for n in self.g.nodes():
            if self.is_router(n):
                cnf = self.gen_router_config(n)
                with open('%s/%s.cfg' % (self.configsdir, n), 'w') as f:
                    f.write(cnf)
            elif self.is_network(n):
                cnf = self.gen_networkns(n)
                with open('%s/%s.sh' % (self.scriptsdir, n), 'w') as f:
                    f.write(cnf)

        import networkx as nx
        gg = nx.DiGraph()
        for node, attrs in self.g.nodes(data=True):
            label = node
            if 'loaddr' in attrs:
                label = "%s\n%s" % (node, attrs['loaddr'])
            gg.add_node(node, label=label)

        for src, dst in self.g.edges():
            gg.add_edge(src, dst)
        nx.write_dot(gg, '%s/g.dot' % self.outdir)

    def is_peer(self, node):
        return self.g.node[node][VERTEX_TYPE] == PEER_TYPE

    def is_local_router(self, node):
        return self.g.node[node][VERTEX_TYPE] == NODE_TYPE

    def is_origin_router(self, node):
        return self.g.node[node][VERTEX_TYPE] == ORIGIN_TYPE

    def is_network(self, node):
        return self.g.node[node][VERTEX_TYPE] == NETWORK_TYPE

    def is_router(self, node):
        return self.is_peer(node) or self.is_local_router(node) or\
               self.is_origin_router(node)

    def local_routers_iter(self):
        for node in self.g.nodes():
            if self.is_local_router(node):
                yield node

    def peers_iter(self):
        for node in self.g.nodes():
            if self.is_peer(node):
                yield node

    def router_iter(self):
        for node in self.g.nodes():
            if self.is_router(node):
                yield node

    def annotate_node(self, n):
        """
        For each router annotate it with topological information needed to
        generate the topology file
        """
        if 'dyn' not in self.g.node[n]:
            self.g.node[n]['dyn'] = {}
        dyn = self.g.node[n]['dyn']
        dyn['model'] = self.router_model
        dyn['console'] = self.next_console.next()
        dyn['cnfg'] = "configs/%s.cfg" % n

        iface_count = 0
        for neighbor in self.g.neighbors(n):
            iface = "f%d/%d" % (iface_count // 2 , iface_count % 2)
            self.g[n][neighbor]['iface'] = iface
            self.g[n][neighbor]['iface_desc'] = ''"To {}"''.format(neighbor)
            iface_count += 1

    def annotate_network(self, n):
        assert len(self.g.neighbors(n)) == 1
        router = self.g.neighbors(n)[0]
        iface = '{node}-veth1'.format(node=n)
        riface = '{node}-veth0'.format(node=n)
        self.g[n][router]['iface'] = iface
        self.g[n][router]['riface'] = riface

    def assign_ip_addresses(self):
        """
        Assign IP addresses to the router interfaces
        Currently we assign /31 IP addresses for each directly connected
        interfaces
        """
        net = ipaddress.ip_network(u'10.0.0.0/31')

        for src, dst in self.g.edges():
            # Check if address already assigned
            if self.g[src][dst].get('addr', None): continue
            if not self.is_router(src): continue
            if self.is_router(dst):
                a1, a2 = [i for i in net]
                self.g[src][dst]['addr'] = a1
                self.g[dst][src]['addr'] = a2
                self.g[src][dst]['net'] = net
                self.g[dst][src]['net'] = net
                # Increment the network addresses for the next round
                nextip = ipaddress.ip_address(IP2Int(str(a2)) + 1)
                net = ipaddress.ip_network(u'%s/31' % nextip)
            elif self.is_network(dst):
                assert dst in self.network_addr_map, "Network %s is not assigned an address" % dst
                net2 = ipaddress.ip_network(self.network_addr_map[dst])
                if net2.prefixlen == 31:
                    a1, a2 = [i for i in net2][0:2]
                else:
                    a1, a2 = [i for i in net2][1:3]
                #iter = net2.__iter__()
                #iter.next()
                #a1 = iter.next()
                #a2 = iter.next()
                self.g[src][dst]['addr'] = a1
                self.g[dst][src]['addr'] = a2
                self.g[src][dst]['net'] = net2
                self.g[dst][src]['net'] = net2
                add_bgp_announces(self.g, src, dst, net=net2)

    def assign_loopback(self):
        """Create loopback interfaces to facilate the iBGP sessions"""
        net = ipaddress.ip_network(u'1.1.1.1/32')
        for node in sorted(list(self.router_iter())):
            a1 = [i for i in net][0]
            self.g.node[node]['lo'] = 'Loopback 0'
            self.g.node[node]['loaddr'] = a1
            self.g.node[node]['lonet'] = net
            # Increment the network addresses for the next round
            nextip = ipaddress.ip_address(IP2Int(str(a1)) + 1)
            net = ipaddress.ip_network(u'%s/32' % nextip)

    def _get_ospf_config(self, node):
        config = ""
        # Announces everything on OSPF
        config += "!\nrouter ospf 100\n"
        config += "  log-adjacency-changes\n"
        config += "  network 0.0.0.0 255.255.255.255 area 0\n"
        config += "!\n"
        return config

    def _get_iface_config(self, node):
        config = ""
        for neighbor in self.g.neighbors(node):
            #if not self.is_router(neighbor): continue
            siface = self.g[node][neighbor]['iface']
            config += 'interface %s\n' % siface
            addr = self.g[node][neighbor]['addr']
            net = self.g[node][neighbor]['net']
            cost = self.g[node][neighbor].get('ospf_cost', None)
            config += " ip address %s %s\n" % (addr, net.netmask)
            if cost:
                config += " ip ospf cost %s\n" % (cost)
            config += ' description "{}"\n'.format(self.g[node][neighbor]['iface_desc'])
            config += " speed auto\n"
            config += " duplex auto\n"

        # Loop back interface
        name = self.g.node[node]['lo']
        addr = self.g.node[node]['loaddr']
        net = self.g.node[node]['lonet']
        config += 'interface %s\n' % name
        config += " ip address %s %s\n" % (addr, net.netmask)
        return config

    def _get_hostnames(self):
        config = ""
        for n, attrs in self.g.nodes(data=True):
            addrs = []
            if 'loaddr' in attrs:
                addrs.append(attrs['loaddr'])
            for neighbor in self.g.neighbors(n):
                addr = self.g[n][neighbor]['addr']
                addrs.append(addr)
            addresses = ' '.join([str(a) for a in addrs])
            config += "ip host {name} {addresses}\n".format(name=n, addresses=addresses)
        return config

    def _get_static_config(self, node):
        config = ""
        if 'static_routes' in self.g.node[node]:
            for route in self.g.node[node]['static_routes']:
                net = route[0]
                if isinstance(net, basestring):
                    net = ipaddress.ip_network(self.network_addr_map[route[0]])
                siface = self.g[node][route[-1]]['iface']
                config += "ip route {ip} {mask} {iface}\n".format(
                    ip=net.network_address, mask=net.netmask, iface=siface)
        return config

    def get_neighbor_address(self, node, neighbor):
        if neighbor in self._nexthop_to_router:
            neighbor = self._nexthop_to_router[neighbor]
        nodeas = get_bgp_asnum(self.g, node)
        neighboras = get_bgp_asnum(self.g, neighbor)
        # For iBGP use loopback iface, otherwise use direct connection
        if nodeas == neighboras:
            #print "Returning loop back address for", node, neighbor
            return self.g.node[neighbor]['loaddr']
        else:
            #print "Returning loop back address for", neighbor, node
            return self.g[neighbor][node]['addr']

    def _get_route_map(self, map_name, mline, print_continue):
        config = "route-map %s %s %s\n" % (map_name, mline.Access, mline.LineNo)
        if mline.Match:
            config += " match %s\n" % mline.Match
        if mline.Action:
            config += " %s\n" % mline.Action
        if print_continue:
            config += ' continue\n'
        config += '!\n'
        return config

    def _get_bgp_config(self, node):
        config = "!\n"
        #export_tags = self.get_node_export_tags(node)
        #community_lists = self.get_community_lists(node)
        neighbors = get_bgp_neighbors(self.g, node)
        as_num = get_bgp_asnum(self.g, node)
        iplists = get_ip_prefix_lists(self.g, node)

        for name, iplist in iplists.iteritems():
            l = [str(self.network_addr_map[ip]) for ip in iplist.Prefixes]
            config += "ip prefix-list %s %s %s\n" % (name, iplist.Action, ' '.join(l))
        config += '!\n'

        for neighbor in neighbors:
            # Import tags
            import_tags = get_node_import_tags(self.g, node, neighbor)
            for tag, val in import_tags.iteritems():
                if isinstance(val, TagPrefixes):
                    map_match = 'ip address prefix %s ' % val.Prefixes.Name
                    map_action = 'set community %s additive' % tag.to_community()
                    add_input_filter(self.g, node, neighbor, 'permit', map_match, map_action)
                elif isinstance(val, TagIncomingRoutes):
                    map_match = None
                    map_action = 'set community %s additive' % tag.to_community()
                    add_input_filter(self.g, node, neighbor, 'permit',
                                     map_match, map_action)
            # Import Local Prefs
            localprefs = get_bgp_neighbor_import_local_prefs(self.g, node, neighbor)
            for pref in localprefs:
                cl = pref.Match.to_match()
                add_community_list(self.g, node, cl)
                map_match = 'community %s' % cl.name
                map_action = 'set local-pref %d' % pref.LocalPref
                add_input_filter(self.g, node, neighbor, 'permit', map_match, map_action)
            # Export Filters
            denyexport = get_bgp_neighbor_export_deny(self.g, node, neighbor)
            for m in denyexport:
                map_match = "community %s" % m.Match.to_match().name
                map_action = None
                add_output_filter(self.g, node, neighbor, 'deny', map_match,
                                 map_action)

        config += "!\n"

        # Community lists
        for name, l in get_community_lists(self.g, node).iteritems():
            config += "%s\n" % l.to_list()

        config += "!\n"

        # Print route maps
        for neighbor, val in neighbors.iteritems():
            inputmaps = get_input_filters(self.g, node, neighbor)
            outputmaps = get_output_filters(self.g, node, neighbor)
            if inputmaps:
                input_map_name = 'MapFrom%s' % neighbor
                input_route_map = SetRouteMap(input_map_name,
                                                      inputmaps)
                val['InputFilter'] = input_route_map
                for i, m in enumerate(inputmaps):
                    cntu = i < len(inputmaps) - 1
                    config += self._get_route_map(input_map_name, m, cntu)
                    config += "!\n"
            if outputmaps:
                output_map_name = 'MapTo%s' % neighbor
                output_route_map = SetRouteMap(output_map_name,
                                                       inputmaps)
                val['OutputFilter'] = output_route_map
                for i, m in enumerate(outputmaps):
                    cntu = i < len(outputmaps) - 1
                    config += self._get_route_map(output_map_name, m, cntu)
                    config += "!\n"
        config += "!\n"

        # Print Route maps for announced perfixes
        prefix_tags = {}
        nextann = 1
        for name, vals in get_bgp_announces(self.g, node).iteritems():
            if not vals.get('tags', None): continue
            tags = vals['tags']
            lineno = 10
            lines = []
            for tag in tags:
                map_match = "ip address prefix %s" %  vals['net']
                map_action = 'set community %s additive' % tag.Tag.to_community()
                lines.append(SetRouteMapLine('permit', lineno, map_match, map_action))
                lineno += 10
            if lines:
                rmap = SetRouteMap('Ann%sTag' % nextann, [lines])
                nextann += 1
                vals['rmap'] = rmap
                for line in lines:
                    config += self._get_route_map(rmap.Name, line, True)
                    config += "!\n"
                config += "!\n"

        #for name, tag in prefix_tags.iteritems():
        #    map_match = "ip address prefix %s" % ' '.join([self.network_addr_map[ip] for ip in tag.Prefixes if ip in get_bgp_announces(self.g, node)])
        #    map_action = 'set community %s additive' % tag.Tag.to_community()
        #    line = SetRouteMapLine('permit', 10, map_match, map_action)
        #    rmap = SetRouteMap('%sTAG' % tag.Tag.name, [line])
        #    config += self._get_route_map(rmap.Name, line, False)
        #    config += "!\n"
        config += "!\n"


        config += "router bgp %d\n" % as_num
        # by default allow add-path functionality
        config += ' bgp log-neighbor-changes\n'
        if self.is_local_router(node):
            config += ' bgp additional-paths send receive\n'

        for name, vals in get_bgp_announces(self.g, node).iteritems():
            net = vals['net']
            if vals.get('rmap', None):
                rmap = vals['rmap']
                rname = rmap.Name
                config += " network {} mask {} route-map {}\n".format(net.network_address,
                                                         net.netmask, rname)
            else:
                config += " network {} mask {}\n".format(net.network_address, net.netmask)

        for neighbor, val in neighbors.iteritems():
            # Establish neigbors
            neighboraddr = self.get_neighbor_address(node, neighbor)
            remoteas = get_bgp_neighbor_remoteas(self.g, node, neighbor)
            loaddr = self.g.node[node]['lo']
            config += " neighbor %s remote-as %s\n" % (neighboraddr, remoteas)
            if int(remoteas) == int(as_num):
                config += " neighbor %s send-community\n" % neighboraddr
                config += " neighbor {} update-source {}\n".format(neighboraddr, loaddr)
            # Add Input filters
            if val.get('InputFilter', None):
                config += " neighbor %s route-map %s in\n" % (neighboraddr, val['InputFilter'].Name)
            # Add Output Filters
            if val.get('OutputFilter', None):
                config += " neighbor %s route-map %s out\n" % (neighboraddr, val['OutputFilter'].Name)

        return config

    def gen_router_config(self, node):
        preamble =  ["version 15.2",
                     "service timestamps debug datetime msec",
                     "service timestamps log datetime msec",
                     "boot-start-marker",
                     "boot-end-marker",
                     "no aaa new-model",
                     "ip cef",
                     "no ipv6 cef",
                     "multilink bundle-name authenticated",
                     "ip forward-protocol nd",
                     "no ip http server",
                     "no ip http secure-server"
                     ]
        end = ['!', '!', 'control-plane', '!', '!', 'line con 0', ' stopbits 1',
               'line aux 0',' stopbits 1', 'line vty 0 4',' login', '!', 'end']

        config = ""
        config += "\n!\nhostname {node}\n!\n".format(node=node)
        config += self._get_hostnames()
        config += "!\n"
        config += self._get_iface_config(node)
        config += "!\n"
        config += "!\n"
        config += "!\n"
        config += self._get_static_config(node)
        config += "!\n"
        if self.gen_ospf and self.is_local_router(node):
            config += self._get_ospf_config(node)
        config += "!\n"
        if self.gen_bgp:
            config += self._get_bgp_config(node)
        return "!\n" + "\n!\n".join(preamble) + config + "\n".join(end)

    def gen_networkns(self, n):
        assert len(self.g.neighbors(n)) == 1
        router = self.g.neighbors(n)[0]
        addr = self.g[n][router]['addr']
        net = self.g[n][router]['net']
        gateway = self.g[router][n]['addr']
        iface = self.g[n][router]['iface']
        riface = self.g[n][router]['riface']

        out = '#!/bin/bash\n'
        out += "# Cleanup first\n"
        out += "sudo ip netns del {node} &>/dev/null\n".format(node=n)
        out += "sudo ip link del {riface} &>/dev/null\n".format(node=n, riface=riface)
        out += "\n"
        out += "sudo ip netns add {node}\n".format(node=n)
        out += "sudo ip link add {riface} type veth peer name {iface}\n".format(node=n, riface=riface, iface=iface)
        out += "sudo ip link set {iface} netns {node}\n".format(iface=iface, node=n)
        out += "sudo ip netns exec {node} ip addr add {ipaddr}/{prefixlen} dev {iface}\n".format(
            node=n, ipaddr=addr, prefixlen=net.prefixlen, iface=iface)
        out += "sudo ip netns exec {node} ip link set {iface} up\n".format(node=n, iface=iface)
        out += "sudo ip netns exec {node} ip route add default via {gw}\n".format(node=n, gw=gateway)
        out += "sudo ifconfig {riface} up\n".format(riface=riface)
        return out

    def generate_topo(self):
        topo = ""
        topo += "autostart = False\n"
        topo += "ghostios = True\n"
        topo += "sparsemem = False\n"
        topo += "[%s]\n" % self.local_dynampis
        topo += "\tworkingdir = %s\n" % self.workingdir
        topo += "\tudp = 15000"
        topo += "\n"
        topo += "\t[[ %s ]]\n" % self.router_model
        for k, v in self.router_info.iteritems():
            topo += "\t\t%s = %s\n" % (k, v)
        for node in sorted(list(self.router_iter())):
            topo += "\t[[ ROUTER %s ]]\n" % node
            for k, v in self.g.node[node]['dyn'].iteritems():
                topo += "\t\t%s = %s\n" % (k, v)
            for neighbor in self.g.neighbors(node):
                if self.is_router(neighbor):
                    siface = self.g[node][neighbor]['iface']
                    diface = self.g[neighbor][node]['iface']
                    topo += "\t\t%s = %s %s\n" % (siface, neighbor, diface)
                elif self.is_network(neighbor):
                    siface = self.g[node][neighbor]['iface']
                    #diface = self.g[neighbor][node]['iface']
                    diface = self.g[neighbor][node]['riface']
                    topo += "\t\t%s = NIO_linux_eth:%s\n" % (siface, diface)
                #topo += "\t\t%s = %s\n" % (self.g[node][neighbor]['addr'], self.g[neighbor][node]['addr'])
        return topo
