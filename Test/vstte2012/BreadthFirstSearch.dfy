class BreadthFirstSearch<Vertex(==)>
{
  // The following function is left uninterpreted (for the purpose of the 
  // verification problem, it can be thought of as a parameter to the class)
  function method Succ(x: Vertex): set<Vertex>

  // This is the definition of what it means to be a path "p" from vertex 
  // "source" to vertex "dest"
  function IsPath(source: Vertex, dest: Vertex, p: seq<Vertex>): bool
  {
    if source == dest then
      p == []
    else
      p != [] && dest in Succ(p[|p|-1]) && IsPath(source, p[|p|-1], p[..|p|-1])
  }

  function IsClosed(S: set<Vertex>): bool  // says that S is closed under Succ
  {
    forall v :: v in S ==> Succ(v) <= S
  }

  // This is the main method to be verified.  Note, instead of using a 
  // postcondition that talks about that there exists a path (such that ...), 
  // this method returns, as a ghost out-parameter, that existential 
  // witness.  The method could equally well have been written using an 
  // existential quantifier and no ghost out-parameter.
  method BFS(source: Vertex, dest: Vertex, ghost AllVertices: set<Vertex>) 
         returns (d: int, ghost path: seq<Vertex>)
    // source and dest are among AllVertices
    requires source in AllVertices && dest in AllVertices;  
    // AllVertices is closed under Succ
    requires IsClosed(AllVertices);                         
    // This method has two basic outcomes, as indicated by the sign of "d".  
    // More precisely, "d" is non-negative iff "source" can reach "dest".
    // The following postcondition says that under the "0 <= d" outcome, 
    // "path" denotes a path of length "d" from "source" to "dest":
    ensures 0 <= d ==> IsPath(source, dest, path) && |path| == d;
    // Moreover, that path is as short as any path from "source" to "dest":
    ensures 0 <= d ==> forall p :: IsPath(source, dest, p) ==> |path| <= |p|;
    // Finally, under the outcome "d < 0", there is no path from "source" to "dest":
    ensures d < 0 ==> !exists p :: IsPath(source, dest, p);
  {
    var V, C, N := {source}, {source}, {};
    ghost var Processed, paths := {}, Maplet({source}, source, [], Empty);
    // V - all encountered vertices
    // Processed - vertices reachable from "source" is at most "d" steps
    // C - unprocessed vertices reachable from "source" in "d" steps 
    //     (but no less)
    // N - vertices encountered and reachable from "source" in "d+1" steps 
    //     (but no less)
    d := 0;
    var dd := Zero;
    while (C != {})
      // V, Processed, C, N are all subsets of AllVertices:
      invariant V <= AllVertices && Processed <= AllVertices && C <= AllVertices && N <= AllVertices;
      // source is encountered:
      invariant source in V;
      // V is the disjoint union of Processed, C, and N:
      invariant V == Processed + C + N;
      invariant Processed !! C !! N;  // Processed, C, and N are mutually disjoint
      // "paths" records a path for every encountered vertex
      invariant ValidMap(source, paths);
      invariant V == Domain(paths);
      // shortest paths for vertices in C have length d, and for vertices in N
      // have length d+1
      invariant forall x :: x in C ==> |Find(source, x, paths)| == d;
      invariant forall x :: x in N ==> |Find(source, x, paths)| == d + 1;
      // "dd" is just an inductive-looking way of writing "d":
      invariant Value(dd) == d;
      // "dest" is not reachable for any smaller value of "d":
      invariant dest in R(source, dd, AllVertices) ==> dest in C;
      invariant d != 0 ==> dest !in R(source, dd.predecessor, AllVertices);
      // together, Processed and C are all the vertices reachable in at most d steps:
      invariant Processed + C == R(source, dd, AllVertices);
      // N are the successors of Processed that are not reachable within d steps:
      invariant N == Successors(Processed, AllVertices) - R(source, dd, AllVertices);
      // if we have exhausted C, then we have also exhausted N:
      invariant C == {} ==> N == {};
      // variant:
      decreases AllVertices - Processed;
    {
      // remove a vertex "v" from "C"
      var v := choose C;
      C, Processed := C - {v}, Processed + {v};
      ghost var pathToV := Find(source, v, paths);
    
      if (v == dest) {
        parallel (p | IsPath(source, dest, p))
          ensures |pathToV| <= |p|;
        {
          Lemma_IsPath_R(source, dest, p, AllVertices);
          if (|p| < |pathToV|) {
            // show that this branch is impossible
            ToNat_Value_Bijection(|p|);
            RMonotonicity(source, ToNat(|p|), dd.predecessor, AllVertices);
          }
        }
        return d, pathToV;
      }

      // process newly encountered successors
      var newlyEncountered := set w | w in Succ(v) && w !in V;
      V, N := V + newlyEncountered, N + newlyEncountered;
      paths := UpdatePaths(newlyEncountered, source, paths, v, pathToV);

      if (C == {}) {
        C, N, d, dd := N, {}, d+1, Suc(dd);
      }
    }

    // show that "dest" in not in any reachability set, no matter 
    // how many successors one follows
    parallel (nn)
      ensures dest !in R(source, nn, AllVertices);
    {
      if (Value(nn) < Value(dd)) {
        RMonotonicity(source, nn, dd, AllVertices);
      } else {
        IsReachFixpoint(source, dd, nn, AllVertices);
      }
    }

    // Now, show what what the above means in terms of IsPath.  More 
    // precisely, show that there is no path "p" from "source" to "dest".
    parallel (p | IsPath(source, dest, p))
      // this and the previous two lines will establish the 
      // absurdity of a "p" satisfying IsPath(source, dest, p)
      ensures false;  
    {
      Lemma_IsPath_R(source, dest, p, AllVertices);
      // a consequence of Lemma_IsPath_R is:  
      // dest in R(source, ToNat(|p|), AllVertices)
      // but that contradicts the conclusion of the preceding parallel statement
    }

    d := -1;  // indicate "no path"
  }

  // property of IsPath

  ghost method Lemma_IsPath_Closure(source: Vertex, dest: Vertex, 
                                p: seq<Vertex>, AllVertices: set<Vertex>)
    requires IsPath(source, dest, p) && source in AllVertices && IsClosed(AllVertices);
    ensures dest in AllVertices && forall v :: v in p ==> v in AllVertices;
  {
    if (p != []) {
      var last := |p| - 1;
      Lemma_IsPath_Closure(source, p[last], p[..last], AllVertices);
    }
  }

  // operations on Nat

  function Value(nn: Nat): nat
    ensures ToNat(Value(nn)) == nn;
  {
    match nn
    case Zero => 0
    case Suc(mm) => Value(mm) + 1
  }

  function ToNat(n: nat): Nat
  {
    if n == 0 then Zero else Suc(ToNat(n - 1))
  }

  ghost method ToNat_Value_Bijection(n: nat)
    ensures Value(ToNat(n)) == n;
  {
    // Dafny automatically figures out the inductive proof of the postcondition
  }

  // Reachability

  function R(source: Vertex, nn: Nat, AllVertices: set<Vertex>): set<Vertex>
  {
    match nn
    case Zero => {source}
    case Suc(mm) =>  R(source, mm, AllVertices) + 
                     Successors(R(source, mm, AllVertices), AllVertices)
  }

  function Successors(S: set<Vertex>, AllVertices: set<Vertex>): set<Vertex>
  {
    set w | w in AllVertices && exists x :: x in S && w in Succ(x)
  }

  ghost method RMonotonicity(source: Vertex, mm: Nat, nn: Nat, AllVertices: set<Vertex>)
    requires Value(mm) <= Value(nn);
    ensures R(source, mm, AllVertices) <= R(source, nn, AllVertices);
    decreases Value(nn) - Value(mm);
  {
    if (Value(mm) < Value(nn)) {
      RMonotonicity(source, Suc(mm), nn, AllVertices);
    }
  }

  ghost method IsReachFixpoint(source: Vertex, mm: Nat, nn: Nat, AllVertices: set<Vertex>)
    requires R(source, mm, AllVertices) == R(source, Suc(mm), AllVertices);
    requires Value(mm) <= Value(nn);
    ensures R(source, mm, AllVertices) == R(source, nn, AllVertices);
    decreases Value(nn) - Value(mm);
  {
    if (Value(mm) < Value(nn)) {
      IsReachFixpoint(source, Suc(mm), nn, AllVertices);
    }
  }

  ghost method Lemma_IsPath_R(source: Vertex, x: Vertex, 
                              p: seq<Vertex>, AllVertices: set<Vertex>)
    requires IsPath(source, x, p) && source in AllVertices && IsClosed(AllVertices);
    ensures x in R(source, ToNat(|p|), AllVertices);
  {
    if (p != []) {
      Lemma_IsPath_Closure(source, x, p, AllVertices);
      var last := |p| - 1;
      Lemma_IsPath_R(source, p[last], p[..last], AllVertices);
    }
  }

  // operations on Map's

  function Domain(m: Map<Vertex>): set<Vertex>
  {
//    if m.Maplet? then m.dom else {}
//    if m == Empty then {} else assert m.Maplet?; m.dom
    match m
    case Empty => {}
    case Maplet(dom, t, s, nxt) => dom
  }

  // ValidMap encodes the consistency of maps (think, invariant).
  // An explanation of this idiom is explained in the README file.
  function ValidMap(source: Vertex, m: Map<Vertex>): bool
  {
    match m
    case Empty =>  true
    case Maplet(dom, v, path, next) =>
      v in dom && dom == Domain(next) + {v} &&
      IsPath(source, v, path) &&
      ValidMap(source, next)
  }

  function Find(source: Vertex, x: Vertex, m: Map<Vertex>): seq<Vertex>
    requires ValidMap(source, m) && x in Domain(m);
    ensures IsPath(source, x, Find(source, x, m));
  {
    match m
    case Maplet(dom, v, path, next) =>
      if x == v then path else Find(source, x, next)
  }

  ghost method UpdatePaths(vSuccs: set<Vertex>, source: Vertex, 
                    paths: Map<Vertex>, v: Vertex, pathToV: seq<Vertex>) 
               returns (newPaths: Map<Vertex>)
    requires ValidMap(source, paths);
    requires vSuccs !! Domain(paths);
    requires forall succ :: succ in vSuccs ==> IsPath(source, succ, pathToV + [v]);
    ensures ValidMap(source, newPaths) && Domain(newPaths) == Domain(paths) + vSuccs;
    ensures forall x :: x in Domain(paths) ==> 
                        Find(source, x, paths) == Find(source, x, newPaths);
    ensures forall x :: x in vSuccs ==> Find(source, x, newPaths) == pathToV + [v];
  {
    if (vSuccs == {}) {
      newPaths := paths;
    } else {
      var succ := choose vSuccs;
      newPaths := Maplet(Domain(paths) + {succ}, succ, pathToV + [v], paths);
      newPaths := UpdatePaths(vSuccs - {succ}, source, newPaths, v, pathToV);
    }
  }
}

datatype Map<T> = Empty | Maplet(dom: set<T>, T, seq<T>, next: Map<T>);

datatype Nat = Zero | Suc(predecessor: Nat);
