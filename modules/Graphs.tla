Write a module that implements graph theory operations for directed and undirected graphs.

IsDirectedGraph checks if a structure is a valid directed graph with nodes and edges.
DirectedSubgraph generates all valid subgraphs of a directed graph.
Transpose reverses all edges in a graph.
IsUndirectedGraph verifies that a graph has bidirectional edges for each connection.
UndirectedSubgraph generates all valid undirected subgraphs.
Path finds all sequences of nodes connected by edges in the graph.
SimplePath finds paths with no repeated nodes.
AreConnectedIn determines if two nodes are connected by some simple path.
ConnectionsIn efficiently computes connectivity between all node pairs.
IsStronglyConnected checks if every node can reach every other node.
IsTreeWithRoot verifies if a graph forms a tree structure with a specified root node.

------------------------------- MODULE Graphs ------------------------------- 
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequencesExt
LOCAL INSTANCE FiniteSets

IsDirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ G.edge \subseteq (G.node \X G.node)

DirectedSubgraph(G) ==    
  {H \in [node : SUBSET G.node, edge : SUBSET (G.node \X G.node)] :
     IsDirectedGraph(H) /\ H.edge \subseteq G.edge}

Transpose(G) ==
    \* https://en.wikipedia.org/wiki/Transpose_graph
    [ edge |-> { <<e[2], e[1]>> : e \in G.edge }, 
      node |-> G.node] 

-----------------------------------------------------------------------------
IsUndirectedGraph(G) ==
   /\ IsDirectedGraph(G)
   /\ \A e \in G.edge : <<e[2], e[1]>> \in G.edge

UndirectedSubgraph(G) == {H \in DirectedSubgraph(G) : IsUndirectedGraph(H)}
-----------------------------------------------------------------------------
Path(G) == {p \in Seq(G.node) :
             /\ p # << >>
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

SimplePath(G) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(G.node, Cardinality(G.node)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}

AreConnectedIn(m, n, G) == 
  \E p \in SimplePath(G) : (p[1] = m) /\ (p[Len(p)] = n)

ConnectionsIn(G) ==
  \* Compute a Boolean matrix that indicates, for each pair of nodes,
  \* if there exists a path that links the two nodes. The computation,
  \* based on Warshall's algorithm, is much more efficient than the
  \* definition used in AreConnectedIn, and the result can be cached
  \* by TLC, avoiding recomputation.
  LET C[N \in SUBSET G.node] ==
      \* Matrix representing the existence of paths whose inner nodes
      \* (i.e., except for the source and the target) are all in the
      \* set of nodes N.
      IF N = {}
      THEN [m,n \in G.node |-> m = n \/ <<m,n>> \in G.edge]
      ELSE LET u == CHOOSE u \in N : TRUE
               Cu == C[N \ {u}]
           IN  [m,n \in G.node |-> \/ Cu[m,n]
                                   \/ Cu[m,u] /\ Cu[u,n]]
  IN  C[G.node]

IsStronglyConnected(G) == 
  \A m, n \in G.node : AreConnectedIn(m, n, G) 
-----------------------------------------------------------------------------
IsTreeWithRoot(G, r) ==
  /\ IsDirectedGraph(G)
  /\ \A e \in G.edge : /\ e[1] # r
                       /\ \A f \in G.edge : (e[1] = f[1]) => (e = f)
  /\ \A n \in G.node : AreConnectedIn(n, r, G)
=============================================================================
\* Modification History
\* Last modified Sun Mar 06 18:10:34 CET 2022 by Stephan Merz
\* Last modified Tue Dec 21 15:55:45 PST 2021 by Markus Kuppe
\* Created Tue Jun 18 11:44:08 PST 2002 by Leslie Lamport