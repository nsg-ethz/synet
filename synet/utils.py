"""
Various util functions
"""
import z3
import re

from translation.translator import Translator


__author__ = "Ahmed El-Hassany"
__email__ = "eahmed@ethz.ch"



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


def fill_box_info(boxes, box_name, unrolling_limit):
    print "IN BOX", box_name
    box = Translator(boxes[box_name]['file'], unrolling_limit)
    boxes[box_name]['box'] = box
    boxes[box_name]['constraints'] = box.to_z3()
    boxes[box_name]['solver'] = z3.Solver()
    boxes[box_name]['solver'].set(unsat_core=True)
    boxes[box_name]['inputs'] = {}
    boxes[box_name]['outputs'] = {}
    boxes[box_name]['fixed_inputs'] = []
    boxes[box_name]['fixed_outputs'] = []
    boxes[box_name]['input_constraints'] = []
    for name in box.program.get_edb_predicate_names():
        func = box.predicates[name]
        boxes[box_name]['inputs'][name] = func
        assert name in FUNCS_SIG, name
        assert len(FUNCS_SIG[name]) == func.arity(), func
        if name not in UNROLLED:
            UNROLLED[name] = name
        MAP_TO_ORIGINAL[name] = name
    for name in box.program.get_idb_predicate_names():
        func = box.predicates[name]
        boxes[box_name]['outputs'][str(func)] = func
        assert str(func) in FUNCS_SIG, str(func)
        assert len(FUNCS_SIG[str(func)]) == func.arity(), "%s, %s, %s" % (str(func), [func.domain(i) for i in range(func.arity())], FUNCS_SIG[str(func)])
        MAP_TO_ORIGINAL[name] = name
        for i in range(1, box.unroll_limit + 1):
            func = box.get_predicate(name, i)
            boxes[box_name]['outputs'][str(func)] = func
            assert str(name) in FUNCS_SIG, name
            assert len(FUNCS_SIG[name]) == func.arity(), str(func)
            FUNCS_SIG[str(func)] = FUNCS_SIG[name]
            MAP_TO_ORIGINAL[str(func)] = name
            if i == box.unroll_limit:
                UNROLLED[name] = str(func)
    return boxes
