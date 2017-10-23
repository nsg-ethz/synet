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
```bash
TOPO=gridrand4; REQ=5; PROT=bgp; time ./synet.py -i examples/CAV-experiments/$TOPO-$PROT-$REQ.logic  -r examples/CAV-experiments/$TOPO-$PROT-$REQ-req.logic -m $PROT
```


```bash
TOPO=AttMpls; REQ=1; PROT=bgp; time ./synet.py -i examples/topozoo/$TOPO-$PROT-$REQ.logic  -r examples/topozoo/$TOPO-$PROT-$REQ-req.logic -m $PROT
```


### Provided Examples:
We provide two sets of examples. The first set in `examples/CAV-experiments` is a set of synthesized grid topologies
in addition to Internet2 topology. This set were used in evaluating SyNET for CAV'17 paper.
The second set, are more realistic examples take from [The Internet Topology Zoo](http://www.topology-zoo.org/) and located
at `examples/topozoo`.
