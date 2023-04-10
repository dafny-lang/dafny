// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class BreadthFirstSearch<Vertex(==)>
{
  // The following function is left uninterpreted (for the purpose of the
  // verification problem, it can be thought of as a parameter to the class)
  function Succ(x: Vertex): set<Vertex>

  // This is the definition of what it means to be a path "p" from vertex
  // "source" to vertex "dest"
  ghost predicate IsPath(source: Vertex, dest: Vertex, p: List<Vertex>)
  {
    match p
    case Nil => source == dest
    case Cons(v, tail) => dest in Succ(v) && IsPath(source, v, tail)
  }

  ghost predicate IsClosed(S: set<Vertex>)  // says that S is closed under Succ
  {
    forall v :: v in S ==> Succ(v) <= S
  }

  // This is the main method to be verified.  Note, instead of using a
  // postcondition that talks about that there exists a path (such that ...),
  // this method returns, as a ghost out-parameter, that existential
  // witness.  The method could equally well have been written using an
  // existential quantifier and no ghost out-parameter.
  method {:rlimit 8000} {:vcs_split_on_every_assert} BFS(source: Vertex, dest: Vertex, ghost AllVertices: set<Vertex>)
         returns (d: int, ghost path: List<Vertex>)
    // source and dest are among AllVertices
    requires source in AllVertices && dest in AllVertices;
    // AllVertices is closed under Succ
    requires IsClosed(AllVertices);
    // This method has two basic outcomes, as indicated by the sign of "d".
    // More precisely, "d" is non-negative iff "source" can reach "dest".
    // The following postcondition says that under the "0 <= d" outcome,
    // "path" denotes a path of length "d" from "source" to "dest":
    ensures 0 <= d ==> IsPath(source, dest, path) && length(path) == d;
    // Moreover, that path is as short as any path from "source" to "dest":
    ensures 0 <= d ==> forall p :: IsPath(source, dest, p) ==> length(path) <= length(p);
    // Finally, under the outcome "d < 0", there is no path from "source" to "dest":
    ensures d < 0 ==> !exists p :: IsPath(source, dest, p);
  {
    path := Nil; // avoid indefinite assignment errors
    var V, C, N := {source}, {source}, {};
    ghost var Processed, paths := {}, map[source := Nil];
    assert paths.Keys == {source};
    // V - all encountered vertices
    // Processed - vertices reachable from "source" is at most "d" steps
    // C - unprocessed vertices reachable from "source" in "d" steps
    //     (but no less)
    // N - vertices encountered and reachable from "source" in "d+1" steps
    //     (but no less)
    d := 0;
    assert dest in R(source, d, AllVertices) ==> dest in C by { reveal R(); }
    assert d != 0 ==> dest !in R(source, d-1, AllVertices) by { reveal R(); }
    assert Processed + C == R(source, d, AllVertices) by { reveal R(); }
    assert N == Successors(Processed, AllVertices) - R(source, d, AllVertices) by { reveal R(); }
    while C != {}
      // V, Processed, C, N are all subsets of AllVertices:
      invariant V <= AllVertices && Processed <= AllVertices && C <= AllVertices && N <= AllVertices;
      // source is encountered:
      invariant source in V;
      // V is the disjoint union of Processed, C, and N:
      invariant V == Processed + C + N;
      invariant Processed !! C !! N;  // Processed, C, and N are mutually disjoint
      // "paths" records a path for every encountered vertex
      invariant ValidMap(source, paths);
      invariant V == paths.Keys;
      // shortest paths for vertices in C have length d, and for vertices in N
      // have length d+1
      invariant forall x :: x in C ==> length(Find(source, x, paths)) == d;
      invariant forall x :: x in N ==> length(Find(source, x, paths)) == d + 1;
      // "dest" is not reachable for any smaller value of "d":
      invariant dest in R(source, d, AllVertices) ==> dest in C;
      invariant d != 0 ==> dest !in R(source, d-1, AllVertices);
      // together, Processed and C are all the vertices reachable in at most d steps:
      invariant Processed + C == R(source, d, AllVertices);
      // N are the successors of Processed that are not reachable within d steps:
      invariant N == Successors(Processed, AllVertices) - R(source, d, AllVertices);
      // if we have exhausted C, then we have also exhausted N:
      invariant C == {} ==> N == {};
      // variant:
      decreases AllVertices - Processed;
    {
      // remove a vertex "v" from "C"
      var v :| v in C;
      assert v != dest && C == {v} ==>
        (Processed + {v}) + (N + (set w | w in Succ(v) && w !in V)) == R(source, d+1, AllVertices) by { reveal R(); }
      C, Processed := C - {v}, Processed + {v};
      ghost var pathToV := Find(source, v, paths);

      if v == dest {
        forall p | IsPath(source, dest, p)
          ensures length(pathToV) <= length(p);
        {
          reveal R();
          Lemma_IsPath_R(source, dest, p, AllVertices);
          if length(p) < length(pathToV) {
            // show that this branch is impossible
            RMonotonicity(source, length(p), d-1, AllVertices);
            assert false;
          }
        }
        return d, pathToV;
      }
      assert C != {} ==> Processed + C == R(source, d, AllVertices) by { reveal R(); }

      // process newly encountered successors
      var newlyEncountered := set w | w in Succ(v) && w !in V;
      assert if C == {} then
        Processed + (N + newlyEncountered) == R(source, d+1, AllVertices)
        else Processed + C == R(source, d, AllVertices) by { reveal R(); }
      V, N := V + newlyEncountered, N + newlyEncountered;
      paths := UpdatePaths(newlyEncountered, source, paths, v, pathToV);

      if C == {} {
        C, N, d := N, {}, d+1;
      }

      assert Processed + C == R(source, d, AllVertices) by { reveal R(); }
      assert d != 0 ==> dest !in R(source, d-1, AllVertices);
    }

    // show that "dest" in not in any reachability set, no matter
    // how many successors one follows
    forall n: nat
      ensures dest !in R(source, n, AllVertices);
    {
      reveal R();
      if n < d {
        RMonotonicity(source, n, d, AllVertices);
      } else {
        IsReachFixpoint(source, d, n, AllVertices);
      }
    }

    // Now, show what what the above means in terms of IsPath.  More
    // precisely, show that there is no path "p" from "source" to "dest".
    forall p | IsPath(source, dest, p)
      // this and the previous two lines will establish the
      // absurdity of a "p" satisfying IsPath(source, dest, p)
      ensures false;
    {
      reveal R();
      Lemma_IsPath_R(source, dest, p, AllVertices);
      // a consequence of Lemma_IsPath_R is:
      // dest in R(source, |p|), AllVertices)
      // but that contradicts the conclusion of the preceding forall statement
    }

    d := -1;  // indicate "no path"
  }

  // property of IsPath

  lemma Lemma_IsPath_Closure(source: Vertex, dest: Vertex,
                             p: List<Vertex>, AllVertices: set<Vertex>)
    requires IsPath(source, dest, p) && source in AllVertices && IsClosed(AllVertices);
    ensures dest in AllVertices && forall v :: v in elements(p) ==> v in AllVertices;
  {
    match p {
      case Nil =>
      case Cons(v, tail) =>
        Lemma_IsPath_Closure(source, v, tail, AllVertices);
    }
  }

  // Reachability

  ghost opaque function R(source: Vertex, n: nat, AllVertices: set<Vertex>): set<Vertex>
  {
    if n == 0 then {source} else
    R(source, n-1, AllVertices) + Successors(R(source, n-1, AllVertices), AllVertices)
  }

  ghost function Successors(S: set<Vertex>, AllVertices: set<Vertex>): set<Vertex>
  {
    set w | w in AllVertices && exists x :: x in S && w in Succ(x)
  }

  lemma RMonotonicity(source: Vertex, m: nat, n: nat, AllVertices: set<Vertex>)
    requires m <= n;
    ensures R(source, m, AllVertices) <= R(source, n, AllVertices);
    decreases n - m;
  {
    reveal R();
    if m < n {
      RMonotonicity(source, m + 1, n, AllVertices);
    }
  }

  lemma {:vcs_split_on_every_assert} IsReachFixpoint(source: Vertex, m: nat, n: nat, AllVertices: set<Vertex>)
    requires R(source, m, AllVertices) == R(source, m+1, AllVertices);
    requires m <= n;
    ensures R(source, m, AllVertices) == R(source, n, AllVertices);
    decreases n - m;
  {
    reveal R();
    if m < n {
      IsReachFixpoint(source, m + 1, n, AllVertices);
    }
  }

  lemma Lemma_IsPath_R(source: Vertex, x: Vertex, p: List<Vertex>, AllVertices: set<Vertex>)
    requires IsPath(source, x, p) && source in AllVertices && IsClosed(AllVertices);
    ensures x in R(source, length(p), AllVertices);
  {
    reveal R();
    match p {
      case Nil =>
      case Cons(v, tail) =>
        Lemma_IsPath_Closure(source, x, p, AllVertices);
        Lemma_IsPath_R(source, v, tail, AllVertices);
    }
  }

  // ValidMap encodes the consistency of maps (think, invariant).
  // An explanation of this idiom is explained in the README file.
  ghost predicate ValidMap(source: Vertex, m: map<Vertex, List<Vertex>>)
  {
    forall v :: v in m ==> IsPath(source, v, m[v])
  }

  ghost function Find(source: Vertex, x: Vertex, m: map<Vertex, List<Vertex>>): List<Vertex>
    requires ValidMap(source, m) && x in m;
    ensures IsPath(source, x, Find(source, x, m));
  {
    m[x]
  }

  ghost method UpdatePaths(vSuccs: set<Vertex>, source: Vertex,
                           paths: map<Vertex, List<Vertex>>, v: Vertex, pathToV: List<Vertex>)
               returns (newPaths: map<Vertex, List<Vertex>>)
    requires ValidMap(source, paths);
    requires vSuccs !! paths.Keys;
    requires forall succ :: succ in vSuccs ==> IsPath(source, succ, Cons(v, pathToV));
    ensures ValidMap(source, newPaths) && newPaths.Keys == paths.Keys + vSuccs;
    ensures forall x :: x in paths ==>
                        Find(source, x, paths) == Find(source, x, newPaths);
    ensures forall x :: x in vSuccs ==> Find(source, x, newPaths) == Cons(v, pathToV);
  {
    if vSuccs == {} {
      newPaths := paths;
    } else {
      var succ :| succ in vSuccs;
      newPaths := paths[succ := Cons(v, pathToV)];
      assert newPaths.Keys == paths.Keys + {succ};
      newPaths := UpdatePaths(vSuccs - {succ}, source, newPaths, v, pathToV);
    }
  }
}

datatype List<T> = Nil | Cons(head: T, tail: List)

ghost function length(list: List): nat
{
  match list
  case Nil => 0
  case Cons(_, tail) => 1 + length(tail)
}

ghost function elements<T>(list: List<T>): set<T>
{
  match list
  case Nil => {}
  case Cons(x, tail) => {x} + elements(tail)
}
