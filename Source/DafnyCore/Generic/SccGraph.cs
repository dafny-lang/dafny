// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny {

  public class Graph<Node> where Node : class {
    public enum VisitedStatus { Unvisited, OnStack, Visited }
    public class Vertex {
      public readonly Node N;
      public readonly List<Vertex/*!*/>/*!*/ Successors = new List<Vertex/*!*/>();
      public List<Vertex/*!*/> SccMembers;  // non-null only for the representative of the SCC
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(Successors));
        Contract.Invariant(SccMembers == null || cce.NonNullElements(SccMembers));
      }

      public Vertex SccRepresentative;  // null if not computed

      public int SccPredecessorCount; // valid only for SCC representatives; indicates how many SCCs are [indirect] predecessors of this one
      public int SccId;  // valid only for SCC representatives; indicates position of this representative vertex in the graph's topological sort
      // the following field is used during the computation of SCCs and of reachability
      public VisitedStatus Visited;
      // the following fields are used during the computation of SCCs:
      public int DfNumber;
      public int LowLink;
      // the following field is used during a Reaches computation
      public int Gen;  // generation <= Gen means this vertex has been visited in the current generation

      public Vertex(Node n) {
        N = n;
      }
      public void AddSuccessor(Vertex v) {
        Contract.Requires(v != null);
        Successors.Add(v);
      }
    }

    private void ComputeSccPredecessorCounts() {
      foreach (var vertex in topologicallySortedRepresentatives) {
        vertex.SccPredecessorCount = 0;
      }

      foreach (var vertex in topologicallySortedRepresentatives) {
        var successorSccs = vertex.SccMembers.SelectMany(v => v.Successors.Select(s => s.SccRepresentative)).Distinct();
        foreach (var successor in successorSccs) {
          if (successor != vertex) {
            vertex.SccPredecessorCount = Math.Max(vertex.SccPredecessorCount, successor.SccPredecessorCount + 1);
          }
        }
      }
    }


    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(vertices != null);
      Contract.Invariant(cce.NonNullElements(vertices.Values));
      Contract.Invariant(topologicallySortedRepresentatives == null || cce.NonNullElements(topologicallySortedRepresentatives));
      Contract.Invariant(!sccComputed || topologicallySortedRepresentatives != null);
    }

    Dictionary<Node, Vertex/*!*/>/*!*/ vertices = new Dictionary<Node, Vertex/*!*/>();
    bool sccComputed = false;
    List<Vertex/*!*/> topologicallySortedRepresentatives;  // computed by the SCC computation

    public int SccCount {
      get {
        ComputeSCCs();
        Contract.Assert(topologicallySortedRepresentatives != null);  // follows from postcondition of ComputeSCCs and the object invariant
        return topologicallySortedRepresentatives.Count;
      }
    }
    int generation = 0;

    public Graph() {
    }

    [Pure]
    public IEnumerable<Vertex> GetVertices() {
      return vertices.Values;
    }

    /// <summary>
    /// Idempotently adds a vertex 'n' to the graph.
    /// </summary>
    public void AddVertex(Node n) {
      GetVertex(n);
    }

    /// <summary>
    /// Idempotently adds a vertex 'n' to the graph and then returns the Vertex for it.
    /// </summary>
    Vertex GetVertex(Node n) {
      Contract.Ensures(Contract.Result<Vertex>() != null);

      Vertex v = FindVertex(n);
      if (v == null) {
        v = new Vertex(n);
        vertices.Add(n, v);
        if (sccComputed) {
          Contract.Assert(topologicallySortedRepresentatives != null);  // follows from object invariant
          v.SccRepresentative = v;
          v.SccMembers = new List<Vertex>();
          v.SccMembers.Add(v);
          v.SccId = topologicallySortedRepresentatives.Count;
          v.SccPredecessorCount = 0;
          topologicallySortedRepresentatives.Add(v);
        }
      }
      return v;
    }

    /// <summary>
    /// Returns the vertex for 'n' if 'n' is in the graph.  Otherwise, returns null.
    /// </summary>
    public Vertex FindVertex(Node n) {
      if (vertices.TryGetValue(n, out var v)) {
        Contract.Assert(v != null);  // follows from postcondition of TryGetValue (since 'vertices' maps to the type Vertex!)
        return v;
      } else {
        return null;
      }
    }

    /// <summary>
    /// Idempotently adds vertices 'from' and 'to' the graph, and then
    /// adds an edge from 'from' to 'to'.
    /// </summary>
    public void AddEdge(Node from, Node to) {
      Vertex v0 = GetVertex(from);
      Vertex v1 = GetVertex(to);
      v0.AddSuccessor(v1);
      sccComputed = false;  // the addition of an edge may invalidate any previous computation of the graph's SCCs
    }

    /// <summary>
    /// Idempotently adds 'n' as a vertex and then returns a Node that is the representative element of the
    /// strongly connected component containing 'n'.
    /// </summary>
    public Node GetSCCRepresentative(Node n) {
      return GetSCCRepr(n).N;
    }

    /// <summary>
    /// Idempotently adds 'n' as a vertex.
    /// </summary>
    public int GetSCCRepresentativePredecessorCount(Node n) {
      return GetSCCRepr(n).SccPredecessorCount;
    }

    /// <summary>
    /// Idempotently adds 'n' as a vertex.  Then, returns the number of SCCs before the SCC of 'n' in the
    /// topologically sorting of SCCs.
    /// </summary>
    public int GetSCCRepresentativeId(Node n) {
      return GetSCCRepr(n).SccId;
    }

    Vertex GetSCCRepr(Node n) {
      Contract.Ensures(Contract.Result<Vertex>() != null);

      Vertex v = GetVertex(n);
      ComputeSCCs();
      Contract.Assert(v.SccRepresentative != null);  // follows from what ComputeSCCs does
      return v.SccRepresentative;
    }

    /// <summary>
    /// Returns a list of the topologically sorted SCCs, each represented in the list by its representative node.
    /// </summary>
    public List<Node> TopologicallySortedComponents() {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Node>>()));
      ComputeSCCs();
      Contract.Assert(topologicallySortedRepresentatives != null);  // follows from object invariant
      return topologicallySortedRepresentatives.ConvertAll(v => v.N);
    }

    /// <summary>
    /// Idempotently adds 'n' as a vertex and then returns the set of Node's in the strongly connected component
    /// that contains 'n'.
    /// </summary>
    public List<Node> GetSCC(Node n) {
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Node>>()));
      Vertex v = GetVertex(n);
      ComputeSCCs();
      Vertex repr = v.SccRepresentative;
      Contract.Assert(repr != null && repr.SccMembers != null);  // follows from postcondition of ComputeSCCs
      List<Node> nn = new List<Node>();
      foreach (Vertex w in repr.SccMembers) {
        nn.Add(w.N);
      }
      return nn;
    }

    /// <summary>
    /// Idempotently adds 'n' as a vertex and then returns the size of the set of Node's in the strongly connected component
    /// that contains 'n'.
    /// </summary>
    public int GetSCCSize(Node n) {
      Contract.Ensures(1 <= Contract.Result<int>());

      Vertex v = GetVertex(n);
      ComputeSCCs();
      Vertex repr = v.SccRepresentative;
      Contract.Assert(repr != null && repr.SccMembers != null);  // follows from postcondition of ComputeSCCs
      return repr.SccMembers.Count;
    }

    /// <summary>
    /// This method sets the SccRepresentative fields of the graph's vertices so that two
    /// vertices have the same representative iff they are in the same strongly connected
    /// component.
    /// As a side effect, this method may change the Visited, DfNumber, and LowLink fields
    /// of the vertices.
    /// </summary>
    void ComputeSCCs() {
      Contract.Ensures(sccComputed);

      if (sccComputed) { return; }  // check if already computed

      // reset all SCC information
      topologicallySortedRepresentatives = new List<Vertex>();
      foreach (Vertex v in vertices.Values) {
        v.Visited = VisitedStatus.Unvisited;
        v.SccMembers = null;
      }
      Stack<Vertex> stack = new Stack<Vertex>();
      int cnt = 0;
      foreach (Vertex v in vertices.Values) {
        if (v.Visited == VisitedStatus.Unvisited) {
          SearchC(v, stack, ref cnt);
        }
      }
      Contract.Assert(cnt == vertices.Count);  // sanity check that everything has been visited

      ComputeSccPredecessorCounts();

      sccComputed = true;
    }

    /// <summary>
    /// This is the 'SearchC' procedure from the Aho, Hopcroft, and Ullman book 'The Design and Analysis of Computer Algorithms'.
    /// </summary>
    void SearchC(Vertex/*!*/ v, Stack<Vertex/*!*/>/*!*/ stack, ref int cnt) {
      Contract.Requires(v != null);
      Contract.Requires(cce.NonNullElements(stack));
      Contract.Requires(v.Visited == VisitedStatus.Unvisited);
      Contract.Requires(topologicallySortedRepresentatives != null);
      Contract.Ensures(v.Visited != VisitedStatus.Unvisited);

      v.DfNumber = cnt;
      cnt++;
      v.LowLink = v.DfNumber;
      stack.Push(v);
      v.Visited = VisitedStatus.OnStack;

      foreach (Vertex w in v.Successors) {
        if (w.Visited == VisitedStatus.Unvisited) {
          SearchC(w, stack, ref cnt);
          v.LowLink = Math.Min(v.LowLink, w.LowLink);
        } else if (w.Visited == VisitedStatus.OnStack) {
          Contract.Assert(w.DfNumber < v.DfNumber || v.LowLink <= w.DfNumber);  // the book also has the guard 'w.DfNumber < v.DfNumber', but that seems unnecessary to me, so this assert is checking my understanding
          v.LowLink = Math.Min(v.LowLink, w.DfNumber);
        }
      }

      if (v.LowLink == v.DfNumber) {
        // The SCC containing 'v' has now been computed.
        v.SccId = topologicallySortedRepresentatives.Count;
        topologicallySortedRepresentatives.Add(v);
        v.SccMembers = new List<Vertex>();
        while (true) {
          Vertex x = stack.Pop();
          x.Visited = VisitedStatus.Visited;
          x.SccRepresentative = v;
          v.SccMembers.Add(x);
          if (x == v) { break; }
        }
      }
    }

    /// <summary>
    /// Return all cycles in the graph.
    /// More precisely, return a maximal set of non-overlapping cycles.
    /// </summary>
    public List<List<Node>> AllCycles() {
      // reset all visited information
      foreach (Vertex v in vertices.Values) {
        v.Visited = VisitedStatus.Unvisited;
      }
      var stack = new List<Vertex>();
      var allCycles = new List<List<Node>>();
      foreach (var v in vertices.Values) {
        Contract.Assert(v.Visited != VisitedStatus.OnStack);
        if (v.Visited == VisitedStatus.Unvisited) {
          AllCycles_aux(v, stack, allCycles);
        }
      }
      return allCycles;
    }

    private void AllCycles_aux(Vertex vertex, List<Vertex> stack, List<List<Node>> cycles) {
      Contract.Requires(vertex != null);
      Contract.Requires(cycles != null);
      Contract.Requires(vertex.Visited == VisitedStatus.Unvisited);
      // requires: everything on "stack" is either Unvisited or OnStack
      Contract.Ensures(vertex.Visited == VisitedStatus.Visited);

      vertex.Visited = VisitedStatus.OnStack;
      stack.Add(vertex);
      foreach (var succ in vertex.Successors) {
        switch (succ.Visited) {
          case VisitedStatus.Visited:
            // ignore this successor
            break;
          case VisitedStatus.Unvisited:
            AllCycles_aux(succ, stack, cycles);
            break;
          case VisitedStatus.OnStack: {
              // We discovered a cycle. succ is somewhere on the stack.
              var s = stack.Count;
              while (true) {
                --s;
                if (stack[s].Visited == VisitedStatus.Visited) {
                  // a cycle involving stack[s] has already been reported, so don't report the new cycle we found
                  break;
                }
                Contract.Assert(stack[s].Visited == VisitedStatus.OnStack);
                if (stack[s] == succ) {
                  // this is where the cycle starts
                  var cycle = new List<Node>();
                  for (int i = s; i < stack.Count; i++) {
                    cycle.Add(stack[i].N);
                    stack[i].Visited = VisitedStatus.Visited;
                  }
                  cycles.Add(cycle);
                  break;
                }
              }
            }
            break;
          default:
            Contract.Assert(false); // unexpected Visited value
            break;
        }
      }
      stack.RemoveAt(stack.Count - 1);  // pop
      vertex.Visited = VisitedStatus.Visited;
    }

    /// <summary>
    /// Returns null if the graph has no cycles.  If the graph does contain some cycle, returns the list of
    /// vertices on one such cycle.
    /// </summary>
    public List<Node> TryFindCycle() {
      // reset all visited information
      foreach (Vertex v in vertices.Values) {
        v.Visited = VisitedStatus.Unvisited;
      }

      foreach (Vertex v in vertices.Values) {
        Contract.Assert(v.Visited != VisitedStatus.OnStack);
        if (v.Visited == VisitedStatus.Unvisited) {
          List<Vertex> cycle = CycleSearch(v);
          if (cycle != null) {
            List<Node> nodes = new List<Node>();
            foreach (Vertex v_ in cycle) {
              nodes.Add(v_.N);
            }
            return nodes;  // a cycle is found
          }
        }
      }
      return null;  // there are no cycles
    }

    /// <summary>
    /// A return of null means there are no cycles involving any vertex in the subtree rooted at v.
    /// A non-null return means a cycle has been found.  Then:
    /// If v.Visited == Visited, then the entire cycle is described in the returned list.
    /// If v.Visited == OnStack, then the cycle consists of the vertices strictly deeper than
    /// w on the stack followed by the vertices (in reverse order) in the returned list, where
    /// w is the first vertex in the list returned.
    /// </summary>
    List<Vertex/*!*/> CycleSearch(Vertex v) {
      Contract.Requires(v != null);
      Contract.Requires(v.Visited == VisitedStatus.Unvisited);
      Contract.Ensures(v.Visited != VisitedStatus.Unvisited);
      Contract.Ensures(Contract.Result<List<Vertex>>() != null || v.Visited == VisitedStatus.Visited);
      Contract.Ensures(Contract.Result<List<Vertex>>() == null || Contract.Result<List<Vertex>>().Count != 0);

      v.Visited = VisitedStatus.OnStack;
      foreach (Vertex succ in v.Successors) {
        // todo:  I would use a 'switch' statement, but there seems to be a bug in the Spec# compiler's type checking.
        if (succ.Visited == VisitedStatus.Visited) {
          // there is no cycle in the subtree rooted at succ, hence this path does not give rise to any cycles
        } else if (succ.Visited == VisitedStatus.OnStack) {
          // we found a cycle!
          List<Vertex> cycle = new List<Vertex>();
          cycle.Add(succ);
          if (v == succ) {
            // entire cycle has been found
            v.Visited = VisitedStatus.Visited;
          }
          return cycle;
        } else {
          Contract.Assert(succ.Visited == VisitedStatus.Unvisited);
          List<Vertex> cycle = CycleSearch(succ);
          if (cycle != null) {
            if (succ.Visited == VisitedStatus.Visited) {
              // the entire cycle has been collected
              v.Visited = VisitedStatus.Visited;
              return cycle;
            } else {
              cycle.Add(succ);
              if (v == cycle[0]) {
                // the entire cycle has been collected and we are the first to find out
                v.Visited = VisitedStatus.Visited;
              }
              return cycle;
            }
          }
        }
      }
      v.Visited = VisitedStatus.Visited;  // there are no cycles from here on
      return null;
    }

    /// <summary>
    /// Returns whether or not 'source' reaches 'sink' in the graph.
    /// 'source' and 'sink' need not be in the graph; if neither is, the return value
    /// is source==sink.
    /// </summary>
    public bool Reaches(Node source, Node sink) {
      Vertex a = FindVertex(source);
      Vertex b = FindVertex(sink);
      if (a == null || b == null) {
        return source.Equals(sink);
      }
      generation++;
      return ReachSearch(a, b);
    }

    bool ReachSearch(Vertex source, Vertex sink) {
      Contract.Requires(source != null);
      Contract.Requires(sink != null);
      if (source == sink) {
        return true;
      } else if (source.Gen == generation) {
        // already visited
        return false;
      } else {
        source.Gen = generation;
        return Contract.Exists(source.Successors, succ => ReachSearch(succ, sink));
      }
    }
  }
}
