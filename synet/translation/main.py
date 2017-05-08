from translator_nonrecursive import Translator

if __name__ == '__main__':
  #boxes_filenames = ['../../logicblox/stratum-01-physical.logic', '../../logicblox/stratum-02-ospf-01.logic', '../../logicblox/stratum-03-ospf-02.logic', '../../logicblox/stratum-04-ibgp-01.logic', '../../logicblox/stratum-05-ibgp-02.logic', '../../logicblox/stratum-06-ibgp-03.logic', '../../logicblox/stratum-07-ibgp-04.logic', '../../logicblox/stratum-08-ibgp-05.logic', '../../logicblox/stratum-09-ibgp-06.logic', '../../logicblox/stratum-10-ibgp-07.logic', '../../logicblox/stratum-11-ibgp-08.logic', '../../logicblox/stratum-12-fwd-01.logic', '../../logicblox/stratum-13-fwd-02.logic', '../../logicblox/stratum-14-fwd-03.logic']
  boxes_filenames = ['../../logicblox/negation_test.logic']
  for box_filename in boxes_filenames:
    print box_filename
    box = Translator(box_filename, 3)
    print box.to_z3()
