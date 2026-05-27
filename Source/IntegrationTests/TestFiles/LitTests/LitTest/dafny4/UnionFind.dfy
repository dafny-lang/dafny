// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment
// Rustan Leino, Nov 2015

// Module M0 gives the high-level specification of the UnionFind data structure
abstract module M0 {
  class Element { }

  class {:autocontracts} UnionFind {
    ghost var M: map<Element, Element>
    ghost predicate Valid() {
      ValidM1()
    }
    ghost predicate {:autocontracts false} ValidM1()
      reads this, Repr
      ensures M == map[] ==> ValidM1()

    constructor ()
      ensures M == map[]
    {
      Repr, M := {this}, map[];
    }

    method New() returns (e: Element)
      ensures old(e !in M && forall e' :: e' in M ==> M[e'] != e)
      ensures M == old(M)[e := e]

    method Find(e: Element) returns (r: Element)
      requires e in M
      ensures M == old(M) && M[e] == r

    method Union(e0: Element, e1: Element) returns (ghost r: Element)
      requires e0 in M && e1 in M
      ensures r in old(M) && old(M[r] == M[e0] || M[r] == M[e1])
      ensures M == map e | e in old(M) :: old(if M[e] == M[e0] || M[e] == M[e1] then r else M[e])
  }
}

// Module M1 gives the concrete data structure used in UnionFind, along with the invariant of
// that data structure.  It also implements the New method and, by declaring a new method Join,
// the Union method.
abstract module M1 refines M0 {
  datatype Contents = Root(depth: nat) | Link(next: Element)
  class Element ... {
    var c: Contents
  }

  type CMap = map<Element, Contents>
  ghost predicate GoodCMap(C: CMap)
  {
    forall f :: f in C && C[f].Link? ==> C[f].next in C
  }

  class UnionFind ... {
    ghost predicate ValidM1()
    {
      M.Keys <= Repr &&
      (forall e :: e in M ==> M[e] in M && M[M[e]] == M[e]) &&
      (forall e :: e in M && e.c.Link? ==> e.c.next in M) &&
      (forall e :: e in M ==> M[e].c.Root? && Reaches(M[e].c.depth, e, M[e], Collect()))
    }

    // This function returns a snapshot of the .c fields of the objects in the domain of M
    ghost function {:autocontracts false} Collect(): CMap
      requires forall f :: f in M && f.c.Link? ==> f.c.next in M
      reads this, set a: Element | a in M
      ensures GoodCMap(Collect())
    {
      map e : Element | e in M :: e.c
    }
    ghost predicate {:autocontracts false} Reaches(d: nat, e: Element, r: Element, C: CMap)
      requires GoodCMap(C)
      requires e in C
    {
      match C[e]
      case Root(_) => e == r
      case Link(next) => d != 0 && Reaches(d-1, next, r, C)
    }
    lemma {:autocontracts false} Reaches_Monotonic(d: nat, e: Element, r: Element, C: CMap, C': CMap)
      requires GoodCMap(C) && GoodCMap(C')
      requires e in C
      requires Reaches(d, e, r, C) && forall f :: f in C ==> f in C' && C[f] == C'[f]
      ensures Reaches(d, e, r, C')
    {
    }

    method New...
    {
      e := new Element;
      e.c := Root(0);
      Repr := Repr + {e};
      M := M[e := e];
      assert Reaches(0, e, e, Collect());
      forall f | f in M
        ensures M[f].c.Root? && Reaches(M[f].c.depth, f, M[f], Collect())
      {
        if f != e {
          Reaches_Monotonic(M[f].c.depth, f, M[f], old(Collect()), Collect());
        }
      }
    }

    method Union...
    {
      var r0 := Find(e0);
      var r1 := Find(e1);
      r := Join(r0, r1);
    }

    method Join(r0: Element, r1: Element) returns (ghost r: Element)
      requires r0 in M && r1 in M && M[r0] == r0 && M[r1] == r1
      ensures r == r0 || r == r1
      ensures M == map e | e in old(M) :: old(if M[e] == r0 || M[e] == r1 then r else M[e])
  }

  // stupid help lemma to get around boxing
  lemma MapsEqual<D>(m: map<D, D>, n: map<D, D>)
    requires forall d :: d in m <==> d in n
    requires forall d :: d in m ==> m[d] == n[d]
    ensures m == n
  {
  }
}

// Module M2 adds the implementation of Find, together with the proofs needed for the verification.
abstract module M2 refines M1 {
  class UnionFind ... {
    method Find...
    {
      r := FindAux(M[e].c.depth, e);
    }

    lemma NextReachesSame(e: Element)
      requires e in M && e.c.Link?
      ensures M[e] == M[e.c.next]
    {
      var next := e.c.next;
      var d0, d1 := M[e].c.depth, M[next].c.depth;
      assert Reaches(d0 - 1, next, M[e], Collect());
      assert Reaches(d1, next, M[next], Collect());
      Reaches_SinkIsFunctionOfStart(d0 - 1, d1, next, M[e], M[next], Collect());
    }

    lemma {:autocontracts false} Reaches_SinkIsFunctionOfStart(d0: nat, d1: nat, e: Element, r0: Element, r1: Element, C: CMap)
      requires GoodCMap(C)
      requires e in C
      requires Reaches(d0, e, r0, C) && Reaches(d1, e, r1, C)
      ensures r0 == r1
    {
    }

    method FindAux(ghost d: nat, e: Element) returns (r: Element)
      requires e in M && Reaches(d, e, M[e], Collect())
      ensures M == old(M) && M[e] == r
      ensures forall d: nat, e, r: Element :: e in old(Collect()) && Reaches(d, e, r, old(Collect())) ==> Reaches(d, e, r, Collect())
    {
      match e.c
      case Root(_) =>
        r := e;
      case Link(next) =>
        NextReachesSame(e);
        r := FindAux(d-1, next);
        ghost var C := Collect();  // take a snapshot of all the .c fields
        e.c := Link(r);
        UpdateMaintainsReaches(d, e, r, C, Collect());
    }

    lemma {:autocontracts false} UpdateMaintainsReaches(td: nat, tt: Element, tm: Element, C: CMap, C': CMap)
      requires GoodCMap(C)
      requires tt in C && Reaches(td, tt, tm, C)
      requires C' == C[tt := Link(tm)] && C'[tt].Link? && tm in C' && C'[tm].Root?
      requires forall f :: f in C && C'[f].Link? ==> C'[f].next in C
      ensures forall d: nat, e, r: Element :: e in C && Reaches(d, e, r, C) ==> Reaches(d, e, r, C')
    {
      forall d: nat, e, r: Element | e in C && Reaches(d, e, r, C)
        ensures Reaches(d, e, r, C')
      {
        ConstructReach(d, e, r, C, td, tt, tm, C');
      }
    }

    lemma {:autocontracts false} ConstructReach(d: nat, e: Element, r: Element, C: CMap, td: nat, tt: Element, tm: Element, C': CMap)
      requires GoodCMap(C)
      requires e in C
      requires Reaches(d, e, r, C)
      requires tt in C && Reaches(td, tt, tm, C)
      requires C' == C[tt := Link(tm)] && C'[tt].Link? && tm in C' && C'[tm].Root?
      requires GoodCMap(C')
      ensures Reaches(d, e, r, C')
    {
      if e == tt {
        Reaches_SinkIsFunctionOfStart(d, td, e, r, tm, C);
      } else {
        match C[e]
        case Root(_) =>
        case Link(next) =>
          ConstructReach(d-1, next, r, C, td, tt, tm, C');
        }
    }
  }
}

// Finally, module M3 adds the implementation of Join, along with what's required to
// verify its correctness.
module M3 refines M2 {
  class UnionFind ... {
    method Join...
    {
      if r0 == r1 {
        r := r0;
        MapsEqual(M, map e | e in M :: if M[e] == r0 || M[e] == r1 then r else M[e]);
        return;
      } else if r0.c.depth < r1.c.depth {
        r0.c := Link(r1);
        r := r1;
        M := map e | e in M :: if M[e] == r0 || M[e] == r1 then r else M[e];
        forall e | e in Collect()
          ensures M[e].c.Root? && Reaches(M[e].c.depth, e, M[e], Collect())
        {
          JoinMaintainsReaches0(r0, r1, old(Collect()), Collect());
          assert Reaches(old(M[e].c).depth, e, old(M)[e], old(Collect()));
        }
      } else if r1.c.depth < r0.c.depth {
        r1.c := Link(r0);
        r := r0;
        M := map e | e in M :: if M[e] == r0 || M[e] == r1 then r else M[e];
        forall e | e in Collect()
          ensures M[e].c.Root? && Reaches(M[e].c.depth, e, M[e], Collect())
        {
          JoinMaintainsReaches0(r1, r0, old(Collect()), Collect());
          assert Reaches(old(M[e].c).depth, e, old(M)[e], old(Collect()));
        }
      } else {
        r0.c := Link(r1);
        r1.c := Root(r1.c.depth + 1);
        r := r1;
        M := map e | e in M :: if M[e] == r0 || M[e] == r1 then r else M[e];
        forall e | e in Collect()
          ensures M[e].c.Root? && Reaches(M[e].c.depth, e, M[e], Collect())
        {
          JoinMaintainsReaches1(r0, r1, old(Collect()), Collect());
          assert Reaches(old(M[e].c).depth, e, old(M)[e], old(Collect()));
        }
      }
    }

    lemma {:autocontracts false} JoinMaintainsReaches1(r0: Element, r1: Element, C: CMap, C': CMap)
      requires GoodCMap(C)
      requires r0 in C && r1 in C && C[r0].Root? && C[r1].Root? && C[r0].depth == C[r1].depth && r0 != r1
      requires C' == C[r0 := Link(r1)][r1 := Root(C[r1].depth + 1)]
      requires GoodCMap(C')
      ensures forall d: nat, e, r: Element {:induction} :: e in C && Reaches(d, e, r, C) && r != r0 && r != r1 ==> Reaches(d, e, r, C')  // proved automatically by induction
      ensures forall e :: e in C && Reaches(C[r0].depth, e, r0, C) ==> Reaches(C'[r1].depth, e, r1, C')
      ensures forall e :: e in C && Reaches(C[r1].depth, e, r1, C) ==> Reaches(C'[r1].depth, e, r1, C')
    {
      forall e | e in C && Reaches(C[r0].depth, e, r0, C)
        ensures Reaches(C'[r1].depth, e, r1, C')
      {
        ExtendedReach'(e, C, C[r0].depth, C'[r1].depth, r0, r1, C');
      }
      forall e | e in C && Reaches(C[r1].depth, e, r1, C)
        ensures Reaches(C'[r1].depth, e, r1, C')
      {
        ReachUnaffectedByChangeFromRoot'(C[r1].depth, e, r1, C, C[r0].depth, r0, r1, C');
      }
    }

    lemma {:autocontracts false} {:induction d, e, r, C} {:nowarn} ReachUnaffectedByChangeFromRoot'(d: nat, e: Element, r: Element, C: CMap, td: nat, r0: Element, r1: Element, C': CMap)
      requires GoodCMap(C)
      requires e in C && Reaches(d, e, r, C)
      requires r0 in C && r1 in C && C[r0].Root? && C[r1].Root? && C[r0].depth == C[r1].depth && r0 != r1
      requires C[r0].Root? && C' == C[r0 := Link(r1)][r1 := Root(C[r1].depth + 1)]
      requires Reaches(td, r0, r0, C) && r0 != r
      requires GoodCMap(C')
      ensures Reaches(d+1, e, r, C')
    {
    }

    lemma {:autocontracts false} ExtendedReach'(e: Element, C: CMap, d0: nat, d1: nat, r0: Element, r1: Element, C': CMap)
      requires GoodCMap(C) && GoodCMap(C')
      requires r0 in C && r1 in C && C[r0].Root? && C[r1].Root? && C[r0].depth == C[r1].depth && r0 != r1
      requires C' == C[r0 := Link(r1)][r1 := Root(C[r1].depth + 1)]
      requires C[r0].Root? && d0 <= C[r0].depth && C[r1].Root? && d1 <= C'[r1].depth && d0 < d1
      requires e in C && Reaches(d0, e, r0, C)
      ensures Reaches(d1, e, r1, C')
    {
      match C[e]
      case Root(_) =>
      case Link(next) =>
        ExtendedReach'(next, C, d0-1, d1-1, r0, r1, C');
    }

    lemma {:autocontracts false} JoinMaintainsReaches0(r0: Element, r1: Element, C: CMap, C': CMap)
      requires GoodCMap(C)
      requires r0 in C && r1 in C && C[r0].Root? && C[r1].Root? && C[r0].depth < C[r1].depth
      requires C' == C[r0 := Link(r1)]
      requires GoodCMap(C')
      ensures forall d: nat, e, r: Element :: e in C && Reaches(d, e, r, C) && r != r0 ==> Reaches(d, e, r, C')
      ensures forall e :: e in C && Reaches(C[r0].depth, e, r0, C) ==> Reaches(C[r1].depth, e, r1, C')
    {
      forall d: nat, e, r: Element | e in C && Reaches(d, e, r, C) && r != r0
        ensures Reaches(d, e, r, C')
      {
        ReachUnaffectedByChangeFromRoot(d, e, r, C, C[r0].depth, r0, r1, C');
      }
      forall e | e in C && Reaches(C[r0].depth, e, r0, C)
        ensures Reaches(C[r1].depth, e, r1, C')
      {
        ExtendedReach(e, C, C[r0].depth, C[r1].depth, r0, r1, C');
      }
    }

    lemma {:autocontracts false} ReachUnaffectedByChangeFromRoot(d: nat, e: Element, r: Element, C: CMap, td: nat, tt: Element, tm: Element, C': CMap)
      requires GoodCMap(C)
      requires e in C && Reaches(d, e, r, C)
      requires tt in C && Reaches(td, tt, tt, C) && tt != r
      requires C[tt].Root? && C' == C[tt := Link(tm)]
      requires GoodCMap(C')
      ensures Reaches(d, e, r, C')
    {
    }

    lemma {:autocontracts false} ExtendedReach(e: Element, C: CMap, d0: nat, d1: nat, r0: Element, r1: Element, C': CMap)
      requires GoodCMap(C) && GoodCMap(C')
      requires r0 in C && r1 in C && r0 != r1
      requires C' == C[r0 := Link(r1)]
      requires C[r0].Root? && d0 <= C[r0].depth && C[r1].Root? && d1 <= C[r1].depth && d0 < d1
      requires e in C && Reaches(d0, e, r0, C)
      ensures Reaches(d1, e, r1, C')
    {
      match C[e]
      case Root(_) =>
      case Link(next) =>
        ExtendedReach(next, C, d0-1, d1-1, r0, r1, C');
    }
  }
}

method Main() {
  var uf := new M3.UnionFind();
  var a := uf.New();
  var b := uf.New();
  var c := uf.New();
  print a == b, "\n";

  var f0 := uf.Find(b);
  var f1 := uf.Find(a);
  print f0 == b, " ", f1 == a, "\n";

  var _ := uf.Union(a, c);
  var g0 := uf.Find(a);
  var g1 := uf.Find(b);
  var g2 := uf.Find(c);
  print g0 == g1, " ", g0 == g2, " ", g1 == b, "\n";
}
