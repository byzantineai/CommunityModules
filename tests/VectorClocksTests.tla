------------------------- MODULE VectorClocksTests -------------------------
EXTENDS VectorClocks, Sequences, Naturals, TLC, Json

ASSUME LET T == INSTANCE TLC IN T!PrintT("VectorClocksTests")

ASSUME IsCausalOrder(<< >>, LAMBDA l: l)
ASSUME IsCausalOrder(<< <<0,0>> >>, LAMBDA l: l)
ASSUME IsCausalOrder(<< <<0,0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausalOrder(<< <<1,0>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME IsCausalOrder(<< <<0>>, <<0,1>> >>, LAMBDA l: l) \* happened before
ASSUME IsCausalOrder(<< <<1>>, <<0,1>> >>, LAMBDA l: l) \* concurrent

ASSUME ~IsCausalOrder(<< <<0,1>>, <<0,0>> >>, LAMBDA l: l)

ASSUME ~IsCausalOrder(<< <<1>>, <<0,0>> >>, LAMBDA l: l) \* concurrent

Log ==
    ndJsonDeserialize("VectorClocksTests.ndjson")

VectorClock(l) ==
    l.pkt.vc

Node(l) ==
    \* ToString is a hack to work around the fact that the Json
     \* module deserializes {"0": 42, "1": 23} into the record
     \* [ 0 |-> 42, 1 |-> 23 ] with domain {"0", "1"} and not
     \* into a function with domain {0, 1}.
    ToString(l.node)

ASSUME ~IsCausalOrder(Log, VectorClock)

ASSUME IsCausalOrder(
			CausalOrder(Log, 
						 VectorClock, 
						 Node,
						 LAMBDA vc: DOMAIN vc), 
			VectorClock)

=============================================================================
