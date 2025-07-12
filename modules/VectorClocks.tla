Write a module for Vector Clocks, which are used to
track causality in distributed systems.

The core concept is the "happened-before" relationship. An event `e1` is said
to have happened before an event `e2` if `e1`'s vector clock is component-wise
less than or equal to `e2`'s, and strictly less in at least one component.
Events that do not have a happened-before relationship in either direction are
considered "concurrent".

The module provides operators for checking and enforcing causal order. The
`IsCausalOrder` operator verifies if a given sequence of events (a log)
adheres to the causal ordering defined by their vector clocks.
The `CausalOrder` operator can be used to sort a log of events, producing one
possible causally consistent sequence.

When comparing vector clocks from different nodes, their domains (the set of
nodes they are aware of) might differ. The operators in this module handle this
by normalizing clocks to a common domain, with a default value of 0 for any
node not present in a clock.
---------------------------- MODULE VectorClocks -------------------------------
EXTENDS Naturals, Sequences, Functions

LOCAL concurrent(v1, v2) ==
    \E i,j \in DOMAIN v1: i # j /\ v1[i] < v2[i] /\ v1[j] > v2[j]

LOCAL happenedBefore(v1, v2) ==
    \* A vector clock v1 is said to happen before v2 if for all nodes, 
     \*  x[n] <= y[n]  , and there exists at least one node such that
     \*  x[h] < y[h].
    /\ \A i \in DOMAIN v1: v1[i] <= v2[i]
    /\ \E i \in DOMAIN v1: v1[i]  < v2[i]

IsCausalOrder(log, clock(_)) ==
    \A i \in 1..Len(log) :
        \A j \in 1..(i - 1) :
            \* Align the vector clocks to the same domain (mapping
             \* missing values to 0).  A node gradually learns about
             \* other nodes, so its clock domain expands over time.
            LET Fill(c, D) == 
                    [ d \in D |-> IF d \in DOMAIN c THEN c[d] ELSE 0 ]
                D   == DOMAIN clock(log[i]) \cup DOMAIN clock(log[j])
                vci == Fill(clock(log[i]), D)
                vcj == Fill(clock(log[j]), D)
            IN happenedBefore(vcj, vci) \/ concurrent(vcj, vci)

CausalOrder(log, clock(_), node(_), domain(_)) ==
    (*
        Sort the provided log by the vector clock values indicated on each line
        of the log. This operator cannot accommodate "hidden" events, meaning
        events that are excluded from the log. The vector clocks must be
        continuous without any gaps.
        
        The predicates clock, node, and domain equals the vector clock from
        a log entry, the node's clock value, and the clock's domain, i.e., the
        nodes for which the clock has values.
        
        Imagine a log containing lines such as:
        
        	[pkt |-> 
        		[vc |-> 
        			[1 |-> 20, 
        			 0 |-> 10,
        			 3 |-> 16, 
        			 7 |-> 21, 
        			 4 |-> 10, 
        			 6 |-> 21]],
        	 node |-> 5,
			 ...
		    ]
		 
		 CausalOrder(log, 
					 	LAMBDA line: line.pkt.vc,
					 	LAMBDA line: line.node,
						LAMBDA vc : DOMAIN vc)
    *)
    CHOOSE newlog \in 
        { f \in 
            [ 1..Len(log) -> Range(log)] : 
                Range(f) = Range(log) } : 
                    IsCausalOrder(newlog, clock)

===============================================================================