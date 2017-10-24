import unittest
from synet.utils import read_all_boxes
from synet.synthesis3 import Synthesizer



BOXES_STATIC = ['fwd01-1-static']
BOXES_OSPF = ['ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']
BOXES_BGP = ['ibgp03', 'ibgp04', 'ibgp05', 'ibgp06', 'ibgp07', 'ibgp08',
             'ibgp09', 'ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0',
             'fwd01-1']


class TestSimple(unittest.TestCase):
    def topo(self, initial_inputs, fixed_outputs, protocol, unrolling_limit=5):
        with open(initial_inputs) as f:
            initial_inputs = f.read()
        with open(fixed_outputs) as f:
            fixed_outputs = f.read()
        if protocol == 'bgp':
            BOXES_ORDER = BOXES_BGP
        elif protocol == 'ospf':
            BOXES_ORDER = BOXES_OSPF
        elif protocol == 'static':
            BOXES_ORDER = BOXES_STATIC
        elif protocol == 'fwd01-1':
            BOXES_ORDER = ['fwd01-1']
        else:
            raise NameError('Unknown synthesis mode')

        boxes = {}
        all_boxes = read_all_boxes()
        for box_name in BOXES_ORDER:
            boxes[box_name] = all_boxes[box_name]
        syn = Synthesizer(boxes, BOXES_ORDER, initial_inputs, fixed_outputs,
                          unrolling_limit=unrolling_limit)

        syn.synthesize()

    @unittest.skip
    def test_Ai3_1_static(self):
        self.topo('examples/topozoo/Ai3-static-1.logic', 'examples/topozoo/Ai3-static-1-req.logic', 'static')

    @unittest.skip
    def test_Ai3_5_static(self):
        self.topo('examples/topozoo/Ai3-static-5.logic', 'examples/topozoo/Ai3-static-5-req.logic', 'static')

    @unittest.skip
    def test_Ai3_1_ospf(self):
        self.topo('examples/topozoo/Ai3-ospf-1.logic', 'examples/topozoo/Ai3-ospf-1-req.logic', 'ospf')

    @unittest.skip
    def test_Ai3_5_ospf(self):
        self.topo('examples/topozoo/Ai3-ospf-5.logic', 'examples/topozoo/Ai3-ospf-5-req.logic', 'ospf')

    @unittest.skip
    def test_Ai3_1_bgp(self):
        self.topo('examples/topozoo/Ai3-bgp-1.logic', 'examples/topozoo/Ai3-bgp-1-req.logic', 'bgp')

    @unittest.skip
    def test_Ai3_5_bgp(self):
        self.topo('examples/topozoo/Ai3-bgp-5.logic', 'examples/topozoo/Ai3-bgp-5-req.logic', 'bgp')

    def test_Ai3_5_fwd01_1(self):
        self.topo('examples/topozoo/Ai3-bgp-5.logic', 'examples/topozoo/Ai3-bgp-5-req.logic', 'fwd01-1')

    @unittest.skip
    def test_I2_1_static(self):
        self.topo('examples/CAV-experiments/i2rand-static-1.logic',
                  'examples/CAV-experiments/i2rand-static-1-req.logic', 'static')

    @unittest.skip
    def test_I2_5_static(self):
        self.topo('examples/CAV-experiments/i2rand-static-5.logic',
                  'examples/CAV-experiments/i2rand-static-5-req.logic', 'static')

    @unittest.skip
    def test_I2_1_ospf(self):
        self.topo('examples/CAV-experiments/i2rand-ospf-1.logic', 'examples/CAV-experiments/i2rand-ospf-1-req.logic',
                  'ospf')

    @unittest.skip
    def test_I2_5_ospf(self):
        self.topo('examples/CAV-experiments/i2rand-ospf-5.logic', 'examples/CAV-experiments/i2rand-ospf-5-req.logic',
                  'ospf')

    @unittest.skip
    def test_I2_1_bgp(self):
        self.topo('examples/CAV-experiments/i2rand-bgp-1.logic', 'examples/CAV-experiments/i2rand-bgp-1-req.logic',
                  'bgp')

    @unittest.skip
    def test_I2_5_bgp(self):
        self.topo('examples/CAV-experiments/i2rand-bgp-5.logic', 'examples/CAV-experiments/i2rand-bgp-5-req.logic',
                  'bgp')

    def test_I2_5_fwd01_1(self):
        self.topo('examples/CAV-experiments/i2rand-bgp-5.logic', 'examples/CAV-experiments/i2rand-bgp-5-req.logic',
                  'fwd01-1')
