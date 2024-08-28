// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --allow-axioms


// ------------ type variables whose values are not inferred ----------

module NonInferredTypeVariables {
  class C<CT> {
    var f: CT
  }

  predicate P<PT>(x: int)
  {
    x < 100
  }

  ghost function Q<QT>(x: int): QT
  {
    var qt :| true; qt
  }

  method M<MT>(n: nat)
  {
    var a := new MT[n];
  }

  method N<NT>(n: nat) returns (x: NT)
  {
    var a := new NT[10];
    x := a[3];
  }

  method DeterminedClient(n: nat)
  {
    ghost var q := Q(n);
    var x := N(n);
    var a := new array;
    var c := new C;
    var s: set;
    var ss := new set[15];

    q := 3.14;  // this will determine the type parameter of Q to be 'real'
    x := 3.14;  // this will determine the type parameter of N to be 'real'
    if a.Length != 0 {
      a[0] := 3.14;  // this will determine the type parameter of 'array' to be 'real'
    }
    c.f := 3.14;  // this will determine the type parameter of 'C' to be 'real'
    var containsPi := 3.14 in s;  // this will determine the type parameter of 'set' to be 'real'
    ss[12] := s;  // this will determine the type parameter of 'array<set< _ >>' to be 'real'
  }

  method BadClient(n: nat)
  {
    var p := P(n);  // error: cannot infer the type argument for P
    ghost var q := Q(n);  // error: cannot infer the type argument for Q (and thus q's type cannot be determined either)
    M(n);  // error: cannot infer the type argument for M
    var x := N(n);  // error: cannot infer the type argument for N (and thus x's type cannot be determined either)
    var a := new array;  // error: cannot infer the type argument for 'array'
    var c := new C;  // error: cannot infer the type argument for 'C'
    var s: set;  // type argument for 'set'
    var ss := new set[15];  // error: cannot infer the type argument in 'array<set< _ >>'
    var what;  // error: the type of this local variable in underspecified
  }

  method MoreBadClient()
  {




    // In the following, the type of the bound variable is completely determined.
    var S: set<set<int>>;
    ghost var d0 := forall s :: s == {7} ==> s != {};
    var d1 := forall s: set :: s in S ==> s == {};
    var ggcc0: C;
    var ggcc1: C;  // error: full type cannot be determined
    ghost var d2 := forall c: C? :: c != null ==> c.f == 10;
    ghost var d2' := forall c: C? :: c == ggcc0 && c != null ==> c.f == 10;
    ghost var d2'' := forall c: C? :: c == ggcc1 && c != null ==> c.f == c.f; // error: here, type of c is not determined

    var d0' := forall s :: s == {7} ==> s != {};
    var d0'' := forall s :: s <= {7} ==> s == {};
  }
}

// -------------- signature completion ------------------

module SignatureCompletion {
  // datatype signatures do not allow auto-declared type parameters on the LHS
  datatype Dt = Ctor(X -> Dt)  // error: X is not a declared type
  datatype Et<Y> = Ctor(X -> Et, Y)  // error: X is not a declared type


  method My0<A,B>(s: set, x: A -> B)
  method My1<A,B>(x: A -> B, s: set)
  method My2<A,B>(s: set, x: A -> B)
  method My3<A,B>(x: A -> B, s: set)

  ghost function F0<A,B>(s: set, x: A -> B): int
  ghost function F1<A,B>(x: A -> B, s: set): int
  ghost function F2<A,B>(s: set, x: A -> B): int
  ghost function F3<A,B>(x: A -> B, s: set): int
}

// -------------- more fields as frame targets --------------------

module FrameTargetFields {
  class C {
    var x: int
    var y: int
    ghost var z: int

    method M()
      modifies this
    {
      var n := 0;
      ghost var save := y;
      while n < x
        modifies `x
      {
        n, x := n + 1, x - 1;
      }
      assert y == save;
    }

    ghost method N()
      modifies this
      modifies `y  // resolution error: cannot mention non-ghost here
      modifies `z  // cool
    {
    }
  }
}

module FrameTargetFields_More {
  class C {
    var x: int
    var y: int
    ghost var z: int
    method P()
      modifies this
    {
      ghost var h := x;
      while 0 <= h
        modifies `x  // resolution error: cannot mention non-ghost here
        modifies `z  // cool
      {
        h, z := h - 1, 5 * z;
      }
    }
  }
}

// ------------------------------------------------------

module AmbiguousModuleReference {
  module A {
    module Inner {
      ghost predicate Q()
    }
  }

  module B {
    module Inner {
      ghost predicate Q()
    }
  }

  module OpenClient {
    import opened A
    import opened B
    lemma M() {
      var a := A.Inner.Q();  // fine
      var b := B.Inner.Q();  // fine
      var p := Inner.Q();  // error: Inner is ambiguous (A.Inner or B.Inner)
    }
  }
}

// --------------------------------------------------

module GhostLet {
  method M() {
    var x: int;
    x := ghost var tmp := 5; tmp;  // error: ghost -> non-ghost
    x := ghost var tmp := 5; 10;  // fine
    x := ghost var a0, a1 :| a0 == 0 && a1 == 1; a0 + a1;  // error: ghost -> non-ghost
    x := ghost var a :| 0 <= a; 10;  // fine
  }
}

// ------------------- tuple equality support -------------------

module TupleEqualitySupport {
  datatype GoodRecord = GoodRecord(set<(int,int)>)
  datatype BadRecord = BadRecord(set<(int, int->bool)>)  // error: this tuple type does not support equality
}

// ------------------- non-type variable names -------------------

module NonTypeVariableNames {
  type X = int

  module Y { }

  method M(m: map<real,string>)
  {
    assert X == X;  // error: type name used as variable
    assert Y == Y;  // error: module name used as variable
    assert X in m;  // error (x2): type name used as variable
    assert Y in m;  // error (x2): module name used as variable
  }

  method N(k: int)
  {
    assert k == X;  // error (x2): type name used as variable
    assert k == Y;  // error (x2): module name used as variable
    X := k;  // error: type name used as variable
    Y := k;  // error: module name used as variable
  }
}

// ------------------- assign-such-that and let-such-that -------------------

module SuchThat {
  method M() {
    var x: int;
    x :| 5 + 7;  // error: constraint should be boolean
    x :| x;  // error: constraint should be boolean
    var y :| 4;  // error: constraint should be boolean
  }
  ghost function F(): int {
    var w :| 6 + 8;  // error: constraint should be boolean
    w
  }
}

// ---------------------- NEW STUFF ----------------------------------------

module GhostTests {
  class G { }

  method GhostNew3(n: nat)
  {
    var g := new G;
    calc {
      5;
      2 + 3;
      { if n != 0 { GhostNew3(n-1); } }  // error: cannot call non-ghost method in a ghost context
      1 + 4;
      { GhostNew4(g); }  // error: cannot call method with nonempty modifies
      -5 + 10;
    }
  }

  ghost method GhostNew4(g: G)
    modifies g
  {
  }

  class MyClass {
    ghost method SideEffect()
      modifies this
    {
    }

    method NonGhostMethod()
    {
    }

    ghost method M()
      modifies this
    {
      calc {
        5;
        { SideEffect(); }  // error: cannot call method with side effects
        5;
      }
    }

    ghost function F(): int
    {
      calc {
        6;
        { assert 6 < 8; }
        { NonGhostMethod(); }  // error: cannot call non-ghost method
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        { MyField := 12; }  // error: cannot assign to a field, and especially not a non-ghost field
        { MyGhostField := 12; }  // error: cannot assign to any field
        { SideEffect(); }  // error: cannot call (ghost) method with a modifies clause
        { var x := 8;
          while x != 0
            modifies this  // error: cannot use a modifies clause on a loop inside a hint
          {
            x := x - 1;
          }
        }
        6;
      }
      5
    }

    var MyField: int
    ghost var MyGhostField: int

    method N()
    {
      var y :=
      calc {
        6;
        { assert 6 < 8; }
        { NonGhostMethod(); }  // error: cannot call non-ghost method
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        { MyField := 12; }  // error: cannot assign to a field, and especially not a non-ghost field
        { MyGhostField := 12; }  // error: cannot assign to any field
        { M(); }  // error: cannot call (ghost) method with a modifies clause
        { var x := 8;
          while x != 0
            modifies this  // error: cannot use a modifies clause on a loop inside a hint
          {
            x := x - 1;
          }
        }
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        6;
      }
      5;
    }
  }
}

module CallsInStmtExpr {
  class MyClass {
    lemma MyLemma()

    ghost method MyEffectlessGhostMethod()

    ghost function UseLemma(): int
    {
      MyEffectlessGhostMethod(); // error: cannot call ghost methods (only lemmas) from this context
      MyLemma();
      10
    }
  }
}

module EvenMoreGhostTests {
  ghost method NiceTry()
    ensures false
  {
    while (true)
      decreases *  // error:  not allowed here
    {
    }
  }

  method BreakMayNotBeFineHere()
  {
    var n := 0;
    var p := 0;
    while (true)
    {
      var dontKnow;
      if (n == 112) {
      } else if (dontKnow == 708) {
        while * {
          label IfNest:
          if (p == 67) {
            break break;  // fine, since this is not a ghost context
          } else if (*) {
            break break break;  // error: tries to break out of more loop levels than there are
          }
        }
      }
    }
  }
}

module BadGhostTransfer {
  datatype DTD_List = DTD_Nil | DTD_Cons(Car: int, Cdr: DTD_List, ghost g: int)

  method DatatypeDestructors_Ghost(d: DTD_List) {
    var g1; g1 := d.g;  // error: cannot use ghost member in non-ghost code
  }

  method AssignSuchThatFromGhost()
  {
    var x: int;
    ghost var g: int;

    x := g;  // error: ghost cannot flow into non-ghost

    x := *;
    assume x == g;  // this mix of ghosts and non-ghosts is cool (but, of course,
                    // the compiler will complain)

    x :| x == g;  // error: left-side has non-ghost, so RHS must be non-ghost as well

    x :| assume x == g;  // this is cool, since it's an assume (but, of course, the
                         // compiler will complain)

    x :| x == 5;
    g :| g <= g;
    g :| assume g < g;  // the compiler will complain here, despite the LHS being
                        // ghost -- and rightly so, since an assume is used
  }
}

module MoreGhostPrintAttempts {
  method TestCalc_Ghost(m: int, n: int, a: bool, b: bool)
  {
    calc {
      n + m;
      { print n + m; } // error: non-ghost statements are not allowed in hints
      m + n;
    }
  }
}

module MoreLetSuchThatExpr {
  method LetSuchThat_Ghost(ghost z: int, n: nat)
  {
    var x; x := var y :| y < z; y;  // error: contraint depend on ghost (z)
  }
}

module UnderspecifiedTypedShouldBeResolvedOnlyOnce {
  method CalcTest0(s: seq<int>) {
    calc {
      2;
      var t :| true; 2;  // error: type of 't' is underspecified
    }
  }
}

module LoopResolutionTests {
  class C {
    var x: int
    ghost var y: int
  }

  ghost method M(c: C)
    modifies c
  {
    var n := 0;
    while n < 100
      modifies c`y
      modifies c`x  // error: not allowed to mention non-ghost field in modifies clause of ghost loops
    {
      c.x := c.x + 1;  // error: assignment to non-ghost field not allowed here
    }
  }

  method MM(c: C)
    modifies c
  {
    var n := 0;
    while
      invariant n <= 100
      modifies c  // regression test
    {
      case n < 100 =>  n := n + 1;
    }
  }

  method MMX(c: C, ghost g: int)
    modifies c
  {
    var n := 0;
    while
      invariant n <= 100
      modifies c`y
      modifies c`x  // error: not allowed to mention non-ghost field in modifies clause of ghost loops
    {
      case n < 100 =>  n := n + 1;  // error: cannot assign to non-ghost in a ghost loop
      case g < 56 && n != 100 => n := n + 1;  // error: cannot assign to non-ghost in a ghost loop
    }
  }

  method MD0(c: C, ghost g: nat)
    modifies c
    decreases *
  {
    var n := 0;
    while n + g < 100
      invariant n <= 100
      decreases *  // error: disallowed on ghost loops
    {
      n := n + 1;  // error: cannot assign to non-ghost in a ghost loop
    }
  }

  method MD1(c: C, ghost g: nat)
    modifies c
    decreases *
  {
    var n := 0;
    while
      invariant n <= 100
      decreases *  // error: disallowed on ghost loops
    {
      case n + g < 100 =>  n := n + 1;  // error: cannot assign to non-ghost in a ghost loop
    }
  }
}

module UnderspecifiedTypesInAttributes {
  function P<T>(x: T): int

  method M() {
    var {:myattr var u :| true; 6} v: int;  // error: type of u is underspecified
    var j {:myattr var u :| true; 6} :| 0 <= j < 100;  // error: type of u is underspecified

    var a := new int[100];
    forall lp {:myattr var u :| true; 6} | 0 <= lp < 100 {  // error: type of u is underspecified
      a[lp] := 0;
    }

    modify {:myattr P(10)} {:myattr var u :| true; 6} a;  // error: type of u is underspecified

    calc {:myattr P(10)} {:myattr var u :| true; 6} // error: type of u is underspecified
    {
      5;
    }
  }
}

module NonInferredTypeVariables' {
  class C<CT> {
    var f: CT
  }

  method MoreBadClient0()
  {
    var b0 := forall s :: s <= {} ==> s == {};  // error: type of s underspecified
    var b1 := forall s: set :: s <= {} ==> s == {};  // error: type of s underspecified
  }
}

module NonInferredTypeVariables'' {
  class C<CT> {
    var f: CT
  }

  method MoreBadClient1()
  {
    var b2 := forall c: C? :: c in {null} ==> c == null;  // error: type parameter of c underspecified
  }
}
