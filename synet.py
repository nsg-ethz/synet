#!/usr/bin/env python

import argparse
import time
import os

#from synet.synthesizer import Synthesizer
from synet.synthesis3 import Synthesizer


def read_all_boxes():
    # Get base dir to find the datalog models
    BASEDIR = os.path.abspath(os.path.join(os.path.abspath(__file__), os.pardir))
    BASEDIR = os.path.join(BASEDIR, 'synet')
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
    return BOXES


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
        BOXES_ORDER = ['ibgp03', 'ibgp04', 'ibgp05', 'ibgp06', 'ibgp07', 'ibgp08', 'ibgp09',
                       'ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']
    elif args.mode == 'ospf':
        BOXES_ORDER = ['ospf01', 'ospf02-0', 'ospf02-1', 'fwd01-0', 'fwd01-1']
    elif args.mode == 'static':
        BOXES_ORDER = ['fwd01-0-static', 'fwd01-1-static']
        BOXES_ORDER = ['fwd01-1-static']
    else:
        raise NameError('Unknown synthesis mode')

    start = time.time()
    boxes = {}
    all_boxes = read_all_boxes()
    for box_name in BOXES_ORDER:
        boxes[box_name] = all_boxes[box_name]
    syn = Synthesizer(boxes, BOXES_ORDER, initial_inputs, fixed_outputs,
                      unrolling_limit=args.unrolling_limit)

    syn.synthesize()
    end = time.time()
    print "XXXXX Synthesis time for %s is %s" % (args.initial_inputs.split('/')[-1].split('.')[0], end - start)
    outdir = "configs/%s" % (args.initial_inputs.split('/')[-1].split('.')[0] + '-configs')
    print "Generating configs to ", outdir
    syn.gen_configs(outdir)


if __name__ == '__main__':
    main()
