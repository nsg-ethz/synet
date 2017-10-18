Steps to use the translator:

- Set the Z3 types in the map: LB_TYPE_TO_Z3_TYPE.

- Set the Z3 constants that may appear in the rules. For exampe, NODE constants go in the map STRING_TO_NODE.

- In the Datalog rule, string constants of the form "<type>_<name>" are interpreted as constants of type <type> and with value <name>. For example, "NODE_R1" is interpreted as a constant of type NODE and value R1. The value "R1" must appear in the map STRING_TO_NODE to be resolved correctly to a Z3 constant.
