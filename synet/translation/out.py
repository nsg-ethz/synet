# ../../logicblox/stratum-01-physical.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
SetNetwork = Function('SetNetwork', Vertex,Vertex,BoolSort())
SetNode = Function('SetNode', Vertex,BoolSort())
SetInterface = Function('SetInterface', Vertex,Vertex,BoolSort())
SetLink = Function('SetLink', Vertex,Vertex,BoolSort())
# Outputs
Node = Function('Node', Vertex,BoolSort())
Node = Function('Node', Vertex,BoolSort())
Node = Function('Node', Vertex,BoolSort())
Interface = Function('Interface', Vertex,BoolSort())
Interface = Function('Interface', Vertex,BoolSort())
Interface = Function('Interface', Vertex,BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
Network = Function('Network', Vertex,BoolSort())
Network = Function('Network', Vertex,BoolSort())
Network = Function('Network', Vertex,BoolSort())
constraints =  [ForAll(A, Node(A) == SetNode(A)), ForAll(A, Interface(A) == (Exists(B, SetInterface(B, A)))), ForAll([A, B],
       EdgePhy(A, B) ==
       Or(SetNetwork(B, A),
          SetLink(A, B),
          SetNetwork(A, B),
          SetInterface(A, B),
          SetInterface(B, A),
          SetLink(B, A))), ForAll(A, Network(A) == (Exists(B, SetNetwork(B, A))))]
# ../../logicblox/stratum-02-ospf-01.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
Node = Function('Node', Vertex,BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
Network = Function('Network', Vertex,BoolSort())
SetOSPFEdgeCost = Function('SetOSPFEdgeCost', Vertex,Vertex,IntSort(),BoolSort())
# Outputs
LinkOSPF = Function('LinkOSPF', Vertex,Vertex,IntSort(),BoolSort())
LinkOSPF = Function('LinkOSPF', Vertex,Vertex,IntSort(),BoolSort())
LinkOSPF = Function('LinkOSPF', Vertex,Vertex,IntSort(),BoolSort())
OSPFRoute_1 = Function('OSPFRoute_1', Vertex,Vertex,Vertex,IntSort(),BoolSort())
OSPFRoute_2 = Function('OSPFRoute_2', Vertex,Vertex,Vertex,IntSort(),BoolSort())
OSPFRoute_3 = Function('OSPFRoute_3', Vertex,Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C],
       LinkOSPF(A, B, C) ==
       (Exists([D, E],
               And(Node(A),
                   Node(B),
                   EdgePhy(A, D),
                   EdgePhy(D, E),
                   EdgePhy(E, B),
                   SetOSPFEdgeCost(D, E, C))))), ForAll([A, B, C, D],
       OSPFRoute_1(A, B, C, D) ==
       Or(Exists([E, F, G],
                 And(Not(EdgePhy(B, A)),
                     Network(A),
                     LinkOSPF(B, C, E),
                     False,
                     D == E + G,
                     D < 100,
                     B != F)),
          And(Network(A),
              LinkOSPF(B, C, D),
              EdgePhy(C, A),
              Network(A)))), ForAll([A, B, C, D],
       OSPFRoute_2(A, B, C, D) ==
       Or(Exists([E, F, G],
                 And(Not(EdgePhy(B, A)),
                     Network(A),
                     LinkOSPF(B, C, E),
                     OSPFRoute_1(A, C, F, G),
                     D == E + G,
                     D < 100,
                     B != F)),
          And(Network(A),
              LinkOSPF(B, C, D),
              EdgePhy(C, A),
              Network(A)))), ForAll([A, B, C, D],
       OSPFRoute_3(A, B, C, D) ==
       Or(Exists([E, F, G],
                 And(Not(EdgePhy(B, A)),
                     Network(A),
                     LinkOSPF(B, C, E),
                     OSPFRoute_2(A, C, F, G),
                     D == E + G,
                     D < 100,
                     B != F)),
          And(Network(A),
              LinkOSPF(B, C, D),
              EdgePhy(C, A),
              Network(A)))), ForAll([A, B, C, D],
       OSPFRoute(A, B, C, D) ==
       Or(Exists([E, F, G],
                 And(Not(EdgePhy(B, A)),
                     Network(A),
                     LinkOSPF(B, C, E),
                     OSPFRoute(A, C, F, G),
                     D == E + G,
                     D < 100,
                     B != F)),
          And(Network(A),
              LinkOSPF(B, C, D),
              EdgePhy(C, A),
              Network(A))))]
# ../../logicblox/stratum-03-ospf-02.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
OSPFRoute = Function('OSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
# Outputs
BestOSPFRoute = Function('BestOSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
BestOSPFRoute = Function('BestOSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
BestOSPFRoute = Function('BestOSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
nonMinOSPFRouteCost = Function('nonMinOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
nonMinOSPFRouteCost = Function('nonMinOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
nonMinOSPFRouteCost = Function('nonMinOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
minOSPFRouteCost = Function('minOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
minOSPFRouteCost = Function('minOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
minOSPFRouteCost = Function('minOSPFRouteCost', Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C, D],
       BestOSPFRoute(A, B, C, D) ==
       And(OSPFRoute(A, B, C, D), minOSPFRouteCost(A, B, D))), ForAll([A, B, C],
       nonMinOSPFRouteCost(A, B, C) ==
       (Exists([D, E, F],
               And(OSPFRoute(A, B, D, C),
                   OSPFRoute(A, B, E, F),
                   F < C)))), ForAll([A, B, C],
       minOSPFRouteCost(A, B, C) ==
       (Exists(D,
               And(OSPFRoute(A, B, D, C),
                   Not(nonMinOSPFRouteCost(A, B, C))))))]
# ../../logicblox/stratum-04-ibgp-01.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
Node = Function('Node', Vertex,BoolSort())
SetBGPLocalPref = Function('SetBGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPAnnouncement = Function('BGPAnnouncement', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
# Outputs
BGPRoute = Function('BGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPRoute = Function('BGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPRoute = Function('BGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPLocalPref = Function('BGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPLocalPref = Function('BGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPLocalPref = Function('BGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
constraints =  [ForAll([A, B, C, D, E],
       BGPRoute(A, B, C, D, E) ==
       (Exists(F,
               And(Node(A), BGPAnnouncement(F, B, C, D, E))))), ForAll([A, B, C, D, E],
       BGPLocalPref(A, B, C, D, E) ==
       Or(SetBGPLocalPref(A, B, C, D, E),
          Exists([F, G, H],
                 And(BGPAnnouncement(F, B, C, D, G),
                     Node(A),
                     Not(SetBGPLocalPref(A, B, C, D, H)),
                     E == 100))))]
# ../../logicblox/stratum-05-ibgp-02.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
BGPLocalPref = Function('BGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
# Outputs
nonMaxBGPLocalPref = Function('nonMaxBGPLocalPref', Vertex,Vertex,IntSort(),BoolSort())
nonMaxBGPLocalPref = Function('nonMaxBGPLocalPref', Vertex,Vertex,IntSort(),BoolSort())
nonMaxBGPLocalPref = Function('nonMaxBGPLocalPref', Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C],
       nonMaxBGPLocalPref(A, B, C) ==
       (Exists([D, E, F, G, H],
               And(BGPLocalPref(A, D, B, E, C),
                   BGPLocalPref(A, F, B, G, H),
                   C < H))))]
# ../../logicblox/stratum-06-ibgp-03.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
SetNetwork = Function('SetNetwork', Vertex,Vertex,BoolSort())
nonMaxBGPLocalPref = Function('nonMaxBGPLocalPref', Vertex,Vertex,IntSort(),BoolSort())
BGPRoute = Function('BGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BGPLocalPref = Function('BGPLocalPref', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
# Outputs
MaxBGPLocalPrefBGPRoute = Function('MaxBGPLocalPrefBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MaxBGPLocalPrefBGPRoute = Function('MaxBGPLocalPrefBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MaxBGPLocalPrefBGPRoute = Function('MaxBGPLocalPrefBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
ConnectedBGPAnnouncement = Function('ConnectedBGPAnnouncement', Vertex,Vertex,Vertex,BoolSort())
ConnectedBGPAnnouncement = Function('ConnectedBGPAnnouncement', Vertex,Vertex,Vertex,BoolSort())
ConnectedBGPAnnouncement = Function('ConnectedBGPAnnouncement', Vertex,Vertex,Vertex,BoolSort())
constraints =  [ForAll([A, B, C, D, E],
       MaxBGPLocalPrefBGPRoute(A, B, C, D, E) ==
       (Exists(F,
               And(BGPLocalPref(A, B, C, D, F),
                   Not(nonMaxBGPLocalPref(A, C, F)),
                   BGPRoute(A, B, C, D, E))))), ForAll([A, B, C],
       ConnectedBGPAnnouncement(A, B, C) ==
       (Exists([D, E],
               And(MaxBGPLocalPrefBGPRoute(A, B, C, D, E),
                   SetNetwork(A, B)))))]
# ../../logicblox/stratum-07-ibgp-04.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
MaxBGPLocalPrefBGPRoute = Function('MaxBGPLocalPrefBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
ConnectedBGPAnnouncement = Function('ConnectedBGPAnnouncement', Vertex,Vertex,Vertex,BoolSort())
# Outputs
ConnectedBGPRoute = Function('ConnectedBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
ConnectedBGPRoute = Function('ConnectedBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
ConnectedBGPRoute = Function('ConnectedBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
constraints =  [ForAll([A, B, C, D, E],
       ConnectedBGPRoute(A, B, C, D, E) ==
       Or(Exists(F,
                 And(Not(ConnectedBGPAnnouncement(A, F, C)),
                     MaxBGPLocalPrefBGPRoute(A, B, C, D, E))),
          And(ConnectedBGPAnnouncement(A, B, C),
              MaxBGPLocalPrefBGPRoute(A, B, C, D, E))))]
# ../../logicblox/stratum-08-ibgp-05.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
ConnectedBGPRoute = Function('ConnectedBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
# Outputs
nonMinAsPath = Function('nonMinAsPath', Vertex,Vertex,IntSort(),BoolSort())
nonMinAsPath = Function('nonMinAsPath', Vertex,Vertex,IntSort(),BoolSort())
nonMinAsPath = Function('nonMinAsPath', Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C],
       nonMinAsPath(A, B, C) ==
       (Exists([D, E, F, G, H],
               And(ConnectedBGPRoute(A, D, B, E, C),
                   ConnectedBGPRoute(A, F, B, G, H),
                   H < C))))]
# ../../logicblox/stratum-09-ibgp-06.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
nonMinAsPath = Function('nonMinAsPath', Vertex,Vertex,IntSort(),BoolSort())
SetNetwork = Function('SetNetwork', Vertex,Vertex,BoolSort())
SetStaticRoute = Function('SetStaticRoute', Vertex,Vertex,Vertex,BoolSort())
SetStaticRouteCost = Function('SetStaticRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
ConnectedBGPRoute = Function('ConnectedBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
BestOSPFRoute = Function('BestOSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
# Outputs
IGPRouteCost = Function('IGPRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
IGPRouteCost = Function('IGPRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
IGPRouteCost = Function('IGPRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
MinAsPathBGPRoute = Function('MinAsPathBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MinAsPathBGPRoute = Function('MinAsPathBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MinAsPathBGPRoute = Function('MinAsPathBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
StaticRouteCost = Function('StaticRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
StaticRouteCost = Function('StaticRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
StaticRouteCost = Function('StaticRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C, D],
       IGPRouteCost(A, B, C, D) ==
       Or(StaticRouteCost(A, B, C, D),
          And(SetNetwork(B, A), D == 0, C == B),
          BestOSPFRoute(A, B, C, D))), ForAll([A, B, C, D, E],
       MinAsPathBGPRoute(A, B, C, D, E) ==
       And(ConnectedBGPRoute(A, B, C, D, E),
           Not(nonMinAsPath(A, C, E)))), ForAll([A, B, C, D],
       StaticRouteCost(A, B, C, D) ==
       Or(Exists(E,
                 And(SetStaticRoute(A, B, C),
                     Not(SetStaticRouteCost(A, B, E, D)),
                     D == 1)),
          And(SetStaticRoute(A, B, C),
              SetStaticRouteCost(A, B, C, D))))]
# ../../logicblox/stratum-10-ibgp-07.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
IGPRouteCost = Function('IGPRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
# Outputs
nonMinIGPCost = Function('nonMinIGPCost', Vertex,Vertex,IntSort(),BoolSort())
nonMinIGPCost = Function('nonMinIGPCost', Vertex,Vertex,IntSort(),BoolSort())
nonMinIGPCost = Function('nonMinIGPCost', Vertex,Vertex,IntSort(),BoolSort())
constraints =  [ForAll([A, B, C],
       nonMinIGPCost(A, B, C) ==
       (Exists([D, E, F],
               And(IGPRouteCost(B, A, D, C),
                   IGPRouteCost(B, A, E, F),
                   F < C))))]
# ../../logicblox/stratum-11-ibgp-08.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
IGPRouteCost = Function('IGPRouteCost', Vertex,Vertex,Vertex,IntSort(),BoolSort())
MinAsPathBGPRoute = Function('MinAsPathBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
nonMinIGPCost = Function('nonMinIGPCost', Vertex,Vertex,IntSort(),BoolSort())
# Outputs
MinIGPBGPRoute = Function('MinIGPBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MinIGPBGPRoute = Function('MinIGPBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
MinIGPBGPRoute = Function('MinIGPBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
constraints =  [ForAll([A, B, C, D, E],
       MinIGPBGPRoute(A, B, C, D, E) ==
       (Exists([F, G],
               And(IGPRouteCost(B, A, F, G),
                   Not(nonMinIGPCost(A, B, G)),
                   MinAsPathBGPRoute(A, B, C, D, E)))))]
# ../../logicblox/stratum-12-fwd-01.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
MinIGPBGPRoute = Function('MinIGPBGPRoute', Vertex,Vertex,Vertex,BitVec(3),IntSort(),BoolSort())
SetAdminDist = Function('SetAdminDist', Vertex,BitVec(3),IntSort(),BoolSort())
SetStaticRoute = Function('SetStaticRoute', Vertex,Vertex,Vertex,BoolSort())
BestOSPFRoute = Function('BestOSPFRoute', Vertex,Vertex,Vertex,IntSort(),BoolSort())
# Outputs
Fwd = Function('Fwd', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Fwd = Function('Fwd', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Fwd = Function('Fwd', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Route = Function('Route', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Route = Function('Route', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Route = Function('Route', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
nonMinCostAD = Function('nonMinCostAD', Vertex,IntSort(),BoolSort())
nonMinCostAD = Function('nonMinCostAD', Vertex,IntSort(),BoolSort())
nonMinCostAD = Function('nonMinCostAD', Vertex,IntSort(),BoolSort())
BestBGPRoute = Function('BestBGPRoute', Vertex,Vertex,Vertex,BoolSort())
BestBGPRoute = Function('BestBGPRoute', Vertex,Vertex,Vertex,BoolSort())
BestBGPRoute = Function('BestBGPRoute', Vertex,Vertex,Vertex,BoolSort())
constraints =  [ForAll([A, B, C, D],
       Fwd(A, B, C, D) ==
       (Exists(E,
               And(Route(A, B, C, D),
                   SetAdminDist(B, D, E),
                   Not(nonMinCostAD(B, E)))))), ForAll([A, B, C, D],
       Route(A, B, C, D) ==
       Or(And(SetStaticRoute(A, B, C), D == 0),
          Exists(E, And(BestOSPFRoute(A, B, C, E), D == 1)))), ForAll([A, B],
       nonMinCostAD(A, B) ==
       (Exists([C, D, E, F, G],
               And(SetAdminDist(A, C, B),
                   Route(D, A, E, F),
                   SetAdminDist(A, F, G),
                   G < B)))), ForAll([A, B, C],
       BestBGPRoute(A, B, C) ==
       (Exists([D, E, F, G],
               And(MinIGPBGPRoute(B, D, A, E, F),
                   Route(D, B, C, G),
                   G != 2))))]
# ../../logicblox/stratum-13-fwd-02.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
Fwd = Function('Fwd', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
# Outputs
OutgoingFwdInterface = Function('OutgoingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
OutgoingFwdInterface = Function('OutgoingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
OutgoingFwdInterface = Function('OutgoingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
IncomingFwdInterface = Function('IncomingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
IncomingFwdInterface = Function('IncomingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
IncomingFwdInterface = Function('IncomingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
constraints =  [ForAll([A, B, C],
       OutgoingFwdInterface(A, B, C) ==
       (Exists([D, E, F],
               And(Fwd(A, B, D, E),
                   EdgePhy(B, C),
                   EdgePhy(C, F),
                   EdgePhy(F, D))))), ForAll([A, B, C],
       IncomingFwdInterface(A, B, C) ==
       (Exists([D, E, F],
               And(Fwd(A, D, C, E),
                   EdgePhy(D, F),
                   EdgePhy(F, B),
                   EdgePhy(B, C)))))]
# ../../logicblox/stratum-14-fwd-03.logic
# sat
from z3 import *
Vertex, all_vertices = EnumSort('Vertex', ['R1',  'R2',  'R3'])
A, B, C, D, E, F = Consts('A B C D E F', Vertex)
# Inputs
Node = Function('Node', Vertex,BoolSort())
IncomingFwdInterface = Function('IncomingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
Network = Function('Network', Vertex,BoolSort())
Fwd = Function('Fwd', Vertex,Vertex,Vertex,BitVec(3),BoolSort())
Interface = Function('Interface', Vertex,BoolSort())
OutgoingFwdInterface = Function('OutgoingFwdInterface', Vertex,Vertex,Vertex,BoolSort())
EdgePhy = Function('EdgePhy', Vertex,Vertex,BoolSort())
# Outputs
EdgeFwd = Function('EdgeFwd', Vertex,Vertex,Vertex,BoolSort())
EdgeFwd = Function('EdgeFwd', Vertex,Vertex,Vertex,BoolSort())
EdgeFwd = Function('EdgeFwd', Vertex,Vertex,Vertex,BoolSort())
ReachFwd_1 = Function('ReachFwd_1', Vertex,Vertex,Vertex,BoolSort())
ReachFwd_2 = Function('ReachFwd_2', Vertex,Vertex,Vertex,BoolSort())
ReachFwd_3 = Function('ReachFwd_3', Vertex,Vertex,Vertex,BoolSort())
ConnectedDirectly = Function('ConnectedDirectly', Vertex,Vertex,BoolSort())
ConnectedDirectly = Function('ConnectedDirectly', Vertex,Vertex,BoolSort())
ConnectedDirectly = Function('ConnectedDirectly', Vertex,Vertex,BoolSort())
constraints =  [ForAll([A, B, C],
       EdgeFwd(A, B, C) ==
       Or(Exists([D, E],
                 And(Fwd(A, C, D, E),
                     Interface(B),
                     EdgePhy(B, C),
                     Not(OutgoingFwdInterface(A, C, B)))),
          Exists([F, G],
                 And(OutgoingFwdInterface(A, F, B),
                     IncomingFwdInterface(A, C, G),
                     EdgePhy(B, C))),
          Exists([H, I],
                 And(Fwd(A, C, H, I),
                     Network(B),
                     EdgePhy(B, C),
                     B != A)),
          And(Network(A),
              Network(B),
              ConnectedDirectly(A, C),
              ConnectedDirectly(B, C),
              B != A),
          OutgoingFwdInterface(A, B, C),
          And(Network(A),
              Node(B),
              Network(C),
              EdgePhy(B, C),
              A == C),
          And(Network(A),
              ConnectedDirectly(A, C),
              Interface(B),
              Not(OutgoingFwdInterface(A, C, B)),
              ConnectedDirectly(B, C)))), ForAll([A, B, C],
       ReachFwd_1(A, B, C) ==
       Or(EdgeFwd(A, B, C),
          Exists(D, And(EdgeFwd(A, B, D), False)))), ForAll([A, B, C],
       ReachFwd_2(A, B, C) ==
       Or(EdgeFwd(A, B, C),
          Exists(D,
                 And(EdgeFwd(A, B, D), ReachFwd_1(A, D, C))))), ForAll([A, B, C],
       ReachFwd_3(A, B, C) ==
       Or(EdgeFwd(A, B, C),
          Exists(D,
                 And(EdgeFwd(A, B, D), ReachFwd_2(A, D, C))))), ForAll([A, B, C],
       ReachFwd(A, B, C) ==
       Or(EdgeFwd(A, B, C),
          Exists(D,
                 And(EdgeFwd(A, B, D), ReachFwd(A, D, C))))), ForAll([A, B],
       ConnectedDirectly(A, B) ==
       And(Node(B), EdgePhy(A, B)))]
