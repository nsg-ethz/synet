#!/usr/bin/env python
"""
Read GraphML topology files from topozoo and generate SyNET inputs
for the topology and the requirements.
"""

import glob
import os
import networkx as nx
from synet.graph_util import read_topology_zoo
from synet.graph_util import topozoo_to_datalog
from synet.graph_util import gen_ospf_reqs
from synet.graph_util import gen_bgp_reqs
from synet.graph_util import gen_static_reqs


__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"


def main():
    for file in glob.glob('examples/topozoo_original/*.graphml'):
        basename = os.path.basename(file)
        toponame = basename.split('.')[0]
        graph = read_topology_zoo(file)
        num_nodes = len(graph.nodes())
        num_edges = len(graph.edges())

        if num_nodes <= 70:
            if not nx.is_strongly_connected(graph):
                # Skip not connected graphs
                continue
            print toponame, num_nodes, num_edges

            for traffic_classes in [1, 5, 10, 15, 20]:
                if traffic_classes >= len(graph.nodes()):
                    continue
                spec = topozoo_to_datalog(graph)
                spec_ospf, reqs_ospf = gen_ospf_reqs(graph, traffic_classes)
                with open('examples/topozoo/%s-ospf-%d.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(spec)
                    f.write(spec_ospf)
                with open('examples/topozoo/%s-ospf-%d-req.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(reqs_ospf)

                spec_bgp, reqs_bgp = gen_bgp_reqs(graph, traffic_classes)
                with open('examples/topozoo/%s-bgp-%d.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(spec)
                    f.write(spec_bgp)
                with open('examples/topozoo/%s-bgp-%d-req.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(reqs_bgp)

                spec_static, reqs_static = gen_static_reqs(graph, traffic_classes)
                with open('examples/topozoo/%s-static-%d.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(spec)
                    f.write(spec_static)
                with open('examples/topozoo/%s-static-%d-req.logic' % (toponame, traffic_classes), 'w') as f:
                    f.write(reqs_static)


if __name__ == '__main__':
    main()
