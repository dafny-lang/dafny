// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --allow-axioms


// ------------------------ inferred type arguments ----------------------------

// Put the following tests in a separate module, so that the method bodies will
// be type checked even if there are resolution errors in other modules.

module NoTypeArgs0 {
  datatype List<+T> = Nil | Cons(T, List)
  datatype Tree<+A,+B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

  method DoAPrefix0<A, B, C>(xs: List) returns (ys: List<A>)
  {
    ys := xs;
  }

  method DoAPrefix1<A, B, C>(xs: List) returns (ys: List<B>)
  {
    ys := xs;  // error: List<B> cannot be assign to a List<A>
  }

  method DoAPrefix2<A, B, C>(xs: List) returns (ys: List<B>)
  {
    ys := xs;  // error: List<B> cannot be assign to a List<A>
  }

  ghost function FTree0(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => x
  }

  ghost function FTree1(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => y  // error: y does not have the right type
  }

  ghost function FTree2<A,B,C>(t: Tree): Tree<A,B>
  {
    t
  }
}

module NoTypeArgs1 {
  datatype Tree<A,B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

  ghost function FTree3<T>(t: Tree): Tree<T,T>  // error: type of 't' does not have enough type parameters
  {
    t
  }
}

// ----------- let-such-that expressions ------------------------

module MiscMisc {
  method LetSuchThat(ghost z: int, n: nat)
  {
    var x: int;
    x := var y :| y < 0; y;  // fine for the resolver (but would give a verification error for not being deterministic)

    x := var w :| w == 2*w; w;  // fine (even for the verifier, this one)
    x := var w := 2*w; w;  // error: the 'w' in the RHS of the assignment is not in scope
    ghost var xg := var w :| w == 2*w; w;
  }
}

// ------------ quantified variables whose types are not inferred ----------

module NonInferredType {
  ghost predicate P<T>(x: T)

  method InferredType(x: int)
  {
    var t;
    assume forall z :: P(z) && z == t;
    assume t == x;  // this statement determines the type of t and z
  }

  method NonInferredType(x: int)
  {
    var t;  // error: the type of t is not determined
    assume forall z :: P(z) && z == t;  // error: the type of z is not determined
  }
}

// ------------ Here are some tests that lemma contexts don't allocate objects -------------

module GhostAllocationTests {
  class G { }
  iterator GIter() { }
  class H { constructor () }
  lemma GhostNew0()
    ensures exists o: G :: fresh(o)
  {
    var p := new G;  // error: lemma context is not allowed to allocate state
    p := new G;  // error: ditto
  }

  method GhostNew1(n: nat, ghost g: int) returns (t: G, z: int)
  {
    if n < 0 {
      z, t := 5, new G;  // fine
    }
    if n < g {
      var tt := new H();  // error: 'new' not allowed in ghost contexts
    }
  }

  method GhostNew2(ghost b: bool)
  {
    if (b) {
      var y := new GIter();  // error: 'new' not allowed in ghost contexts (and a non-ghost method is not allowed to be called here either)
    }
  }
}
module MoreGhostAllocationTests {
  class G { }
  method GhostNew3(n: nat) {
    var g := new G;
    calc {
      5;
      { var y := new G; }  // error: 'new' not allowed in lemma contexts
      2 + 3;
    }
  }
  ghost method GhostNew4(g: G)
    modifies g
  {
  }
}

module NewForallAssign {
  class G { }
  method NewForallTest(n: nat) {
    var a := new G[n];
    forall i | 0 <= i < n {
      a[i] := new G;  // error: 'new' is currently not supported in forall statements
  } }
}
module NewForallProof {
  class G { }
  method NewForallTest(n: nat) { var a := new G[n];
    forall i | 0 <= i < n ensures true { // this makes the whole 'forall' statement into a ghost statement
      a[i] := new G;  // error: proof-forall cannot update state (and 'new' not allowed in ghost contexts, but that's checked at a later stage)
  } }
}

// ------------------------- underspecified types ------------------------------

module UnderspecifiedTypes {
  method M(S: set<int>) {
    var n, p, T0 :| 12 <= n && n in T0 && 10 <= p && p in T0 && T0 <= S && p % 2 != n % 2;
    var T1 :| 12 in T1 && T1 <= S;
    var T2 :| T2 <= S && 12 in T2;

    var T3'0: set<int> :| 120 in T3'0;
    var T3'1: multiset<int> :| 120 in T3'1;
    var T3'2: map<int,bool> :| 120 in T3'2;
    var T3'3: seq<int> :| 120 in T3'3;
    var T3'4: bool :| 120 in T3'4;  // error: second argument to 'in' cannot be bool
    var T4 :| T4 <= S;
  }
}

module UnderspecifiedTypes' {
  method M() {
    var T3 :| 120 in T3;  // error: underspecified type
  }
}

// ------------------------- lemmas ------------------------------

module MiscLemma {
  class L { }

  // a lemma is allowed to have out-parameters, but not a modifies clause
  lemma MyLemma(x: int, l: L) returns (y: int)
    requires 0 <= x
    modifies l
    ensures 0 <= y
  {
    y := x;
  }
}
