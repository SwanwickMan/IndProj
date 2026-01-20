datatype Node = V(id: int)
datatype Edge = E(u: Node, v: Node, w: int)

class Graph {
  var nodes: set<Node>
  var edges: set<Edge>

  constructor()
    ensures nodes == {}
    ensures edges == {}
  {
    nodes := {};
    edges := {};
  }

  method AddNode(n: Node)
    modifies this
    ensures nodes == old(nodes) + {n}
  {
    nodes := nodes + {n};
  }

  method AddEdge(e: Edge)
    requires e.u in nodes && e.v in nodes
    modifies this
    ensures edges == old(edges) + {e}
  {
    edges := edges + {e};
  }

  method ContainsNode(n: Node) returns (b: bool)
    ensures b == (n in nodes)
  {
    b := n in nodes;
  }

  method ContainsEdge(e: Edge) returns (b: bool)
    ensures b == (e in edges)
  {
    b := e in edges;
  }

  ghost predicate Valid() 
    reads this
  {
    forall e :: e in edges ==> e.u in nodes && e.v in nodes
  }
}

method Dijkstra(source: Node) returns (dist: map<Node, int>)
    requires Valid()
    requires source in nodes
    ensures forall n: Node :: n in nodes ==> dist[n] >= 0
    ensures dist[source] == 0
  {
    var unvisited := nodes;
    // Initialize distances: 0 for source, large number for others
    dist := map n: Node | n in nodes :: if n == source then 0 else 1000000;

    while |unvisited| > 0
      invariant Valid()
      invariant unvisited <= nodes
      invariant forall n: Node :: n in nodes ==> dist[n] >= 0
      decreases |unvisited|
    {
      // Pick node with minimum distance in unvisited
      var u: Node := ArbitraryNode(unvisited);
      var best := dist[u];

      // Iterate over unvisited as a sequence
      forall n: Node | n in unvisited
      {
        if dist[n] < best {
          best := dist[n];
          u := n;
        }
      }

      unvisited := unvisited - {u};

      // Relax edges outgoing from u
      forall e: Edge | e in edges
      {
        if e.u == u && e.v in unvisited {
          var alt := dist[u] + e.w;
          if alt < dist[e.v] {
            dist := dist[e.v := alt];
          }
        }
      }
    }
  }
  // Helper to get an arbitrary element from a non-empty set
  function ArbitraryNode(s: set<Node>): Node
    requires |s| > 0
    ensures ArbitraryNode(s) in s
  {
    set#Choose(s)
  }

method main(){
    var x := V(1);


}