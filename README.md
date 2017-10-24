# SyNET

SyNET is a system to synthesis network wide configurations given forwarding requirements.

## SyNET requirements

SyNET depends on the following packages

1. networkx: `pip install networkx`
2. z3 wih python bindings, see https://github.com/Z3Prover/z3


## Running SyNET

SyNET is invoked using the following command

```./synet.py -i TOPO_FILE.logic  -r REQUIREMENTS_FILE.logic -m PROTOCOL```


### Example

A simple example is provided at `examples/simple.logic` of a topology with 3 nodes connected in a triangle shape.
In this example, external BGP traffic is learned via `R2`.
A sample requirement over this topology, is to forward the traffic going externally via the path `R1-R3-R2`.
The requirements are provided in `examples/simple-req.logic`.

To synthesize the configrations for this example, SyNET can be invoked as follow:

```bash
./synet.py -i examples/simple.logic -r examples/simple-req.logic -m bgp
```

The argument `-i` specifies the input topology. The topology is represented as a set of Datalog predicates.
For instance. `+SetNode("R1").` adds a router `R1` to the topology, while `+SetLink("R1_I1", "R2_I1").`
specifics that there is a link between the two interfaces `R1_I1` and `R2_I1`.
_Note_, the `+` at the beginning of the predicate and `.` at the end of it.


The argument `-r` specifices the requirements to be implemented on the given topology.
The requirement uses the same syntax as the topology file.

The argument `-m` specifices which protocols to use: `static` will only use static routes,
`ospf` will used static and OSPF routes, and `bgp` will use static, OSPF and BGP routes.
 



### Provided Examples:
We provide two sets of examples. The first set, in `examples/CAV-experiments`, is a set of synthesized grid topologies
in addition to Internet2 topology. This set were used in evaluating SyNET for CAV'17 paper.

You can run these examples via:

```bash
TOPO=gridrand4; REQ=5; PROT=bgp; time ./synet.py -i examples/CAV-experiments/$TOPO-$PROT-$REQ.logic  -r examples/CAV-experiments/$TOPO-$PROT-$REQ-req.logic -m $PROT
```


The second set, are more realistic examples take from [The Internet Topology Zoo](http://www.topology-zoo.org/) and located
at `examples/topozoo`.

You can run these examples via:

```bash
TOPO=AttMpls; REQ=1; PROT=bgp; time ./synet.py -i examples/topozoo/$TOPO-$PROT-$REQ.logic  -r examples/topozoo/$TOPO-$PROT-$REQ-req.logic -m $PROT
```
