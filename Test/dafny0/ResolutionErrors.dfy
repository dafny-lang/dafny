// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Misc {
  //Should not verify, as ghost loops should not be allowed to diverge.
  method GhostDivergentLoop()
  {
     var a := new int [2];
     a[0] := 1;
     a[1] := -1;
     ghost var i := 0;
     while (i < 2)
        decreases * // error: not allowed on a ghost loop
        invariant i <= 2
        invariant (forall j :: 0 <= j && j < i ==> a[j] > 0)
     {
       i := 0;
     }
     assert a[1] != a[1]; // ...for then this would incorrectly verify
  }

  method ManyIndices<T>(a: array3<T>, b: array<T>, m: int, n: int)
  {
    // the following invalid expressions were once incorrectly resolved:
    var x := a[m, n];        // error
    var y := a[m];           // error
    var z := b[m, n, m, n];  // error
  }

  method SB(b: array2<int>, s: int) returns (x: int, y: int)
    requires b != null;
  {
    while
    {
      case b[x,y] == s =>
    }
  }

  // -------- name resolution

  class Global {
    var X: int;
    function method F(x: int): int { x }
    static function method G(x: int): int { x }
    method M(x: int) returns (r: int)
    {
      r := x + X;
    }
    static method N(x: int) returns (r: int)
    {
      r := x + X;  // error: cannot access instance field X from static method
    }
  }

  method TestNameResolution0() {
    var z: int;
    z := Global.X;  // error: X is an instance field
    z := F(2);  // error: cannot resolve F
    z := Global.F(2);  // error: invocation of instance function requires an instance
    z := G(2);  // error: cannot resolve G
    z := Global.G(2);
    z := M(2);  // error: cannot resolve M
    z := Global.M(2);  // error: call to instance method requires an instance
    z := N(1);  // error: cannot resolve N
    z := Global.N(1);

    z := z(5);  // error: using local as if it were a function
    z := Global.z;  // error: class Global does not have a member z

    var Global: Global;  // a local variable with the name 'Global'
    z := Global.X;  // this means the instance field X of the object stored in the local variable 'Global'
    var gg: Global := null;
    var y := gg.G(5);
    y := gg.N(5);
  }

  datatype Abc = Abel | Benny | Cecilia(y: int) | David(x: int) | Eleanor
  datatype Xyz = Alberta | Benny | Constantine(y: int) | David(x: int)
  datatype Rst = David(x: int, y: int)

  function Tuv(arg0: Abc, arg1: bool): int { 10 }

  class EE {
    var Eleanor: bool;
    method TestNameResolution1() {
      var a0 := Abel;
      var a1 := Alberta;
      var b0 := Benny;  // error: there's more than one constructor with the name Benny; needs qualification
      var b1 := Abc.Benny;
      var b2 := Xyz.Benny;
      var Benny := 15;  // introduce a local variable with the name 'Benny'
      var b3 := Benny;
      var d0 := David(20);  // error: constructor name David is ambiguous
      var d1 := David;  // error: constructor name David is ambiguous (never mind that the signature does
            // not match either of them)
      var d2 := David(20, 40);  // error: constructor name Davis is ambiguous (never mind that the given
              // parameters match the signature of only one of those constructors)
      var d3 := Abc.David(20, 40);  // error: wrong number of parameters
      var d4 := Rst.David(20, 40);
      var e := Eleanor;  // this resolves to the field, not the Abc datatype constructor
      assert Tuv(Abc.Eleanor, e) == 10;
    }
  }
}

// --------------- ghost tests -------------------------------------

module HereAreMoreGhostTests {
  datatype GhostDt =
    Nil(ghost extraInfo: int) |
    Cons(data: int, tail: GhostDt, ghost moreInfo: int)

  class GhostTests {
    method M(dt: GhostDt) returns (r: int) {
      ghost var g := 5;
      r := g;  // error: RHS is ghost, LHS is not
      r := F(18, g);  // error: RHS is a ghost and will not be available at run time
      r := G(20, g);  // it's fine to pass a ghost as a parameter to a non-ghost, because
                      // only the ghost goes away during compilation
      r := N(22, g);  // ditto
      r := N(g, 22);  // error: passing in 'g' as non-ghost parameter
      r := P(24, 22);  // error: 'P' is ghost, but its result is assigned to a non-ghost

      match (dt) {
        case Nil(gg) =>
        case Cons(dd, tt, gg) =>
          r := G(dd, dd);  // fine
          r := G(dd, gg);  // fine
          r := G(gg, gg);  // error: cannot pass ghost 'gg' as non-ghost parameter to 'G'
      }
      var dd;
      dd := GhostDt.Nil(g);  // fine
      dd := GhostDt.Cons(g, dt, 2);  // error: cannot pass 'g' as non-ghost parameter
      ghost var dtg := GhostDt.Cons(g, dt, 2);  // fine, since result is ghost
    }
    function F(x: int, y: int): int {
      y
    }
    function method G(x: int, ghost y: int): int {
      y  // error: cannot return a ghost from a non-ghost function
    }
    function method H(dt: GhostDt): int {
      match dt
      case Nil(gg) =>  gg  // error: cannot return a ghost from a non-ghost function
      case Cons(dd, tt, gg) =>  dd + gg  // error: ditto
    }
    method N(x: int, ghost y: int) returns (r: int) {
      r := x;
    }
    ghost method P(x: int, y: int) returns (r: int) {
      ghost var g := 5;
      r := y;  // allowed, since the entire method is ghost
      r := r + g;  // fine, for the same reason
      r := N(20, 20);  // error: call to non-ghost method from ghost method is not okay
    }
    ghost method BreaksAreFineHere(t: int)
    {
      var n := 0;
      ghost var k := 0;
      while (true)
        invariant n <= 112;
        decreases 112 - n;
      {
        label MyStructure: {
          if (k % 17 == 0) { break MyStructure; }  // this is fine, because it's a ghost method
          k := k + 1;
        }
        label MyOtherStructure:
        if (k % 17 == 0) {
          break MyOtherStructure;
        } else {
          k := k + 1;
        }

        if (n == 112) {
          break;
        } else if (n == t) {
          return;
        }
        n := n + 1;
      }
    }
    method BreakMayNotBeFineHere(ghost t: int)
    {
      var n := 0;
      ghost var k := 0;
      var p := 0;
      while (true)
        invariant n <= 112;
        decreases 112 - n;
      {
        label MyStructure: {
          k := k + 1;
        }
        label MyOtherStructure:
        if (k % 17 == 0) {
          break MyOtherStructure;  // this break is fine
        } else {
          k := k + 1;
        }

        var dontKnow;
        if (n == 112) {
          ghost var m := 0;
          label LoopLabel0:
          label LoopLabel1:
          while (m < 200) {
            if (m % 103 == 0) {
              if {
                case true => break;  // fine, since this breaks out of the enclosing ghost loop
                case true => break LoopLabel0;  // fine
                case true => break LoopLabel1;  // fine
              }
            } else if (m % 101 == 0) {
            }
            m := m + 3;
          }
          break;
        } else if (dontKnow == 708) {
          var q := 0;
          while (q < 1) {
            label IfNest:
            if (p == 67) {
              break break;  // fine, since this is not a ghost context
            }
            q := q + 1;
          }
        } else if (n == t) {
        }
        n := n + 1;
        p := p + 1;
      }
    }
    method BreakMayNotBeFineHere_Ghost(ghost t: int)
    {
      var n := 0;
      ghost var k := 0;
      var p := 0;
      while (true)
        invariant n <= 112;
        decreases 112 - n;
      {
        label MyStructure: {
          if (k % 17 == 0) { break MyStructure; }  // error: break from ghost to non-ghost point
          k := k + 1;
        }
        label MyOtherStructure:
        if (k % 17 == 0) {
          break MyOtherStructure;  // this break is fine
        } else {
          k := k + 1;
        }

        var dontKnow;
        if (n == 112) {
          ghost var m := 0;
          label LoopLabel0:
          label LoopLabel1:
          while (m < 200) {
            if (m % 103 == 0) {
              if {
                case true => break;  // fine, since this breaks out of the enclosing ghost loop
                case true => break LoopLabel0;  // fine
                case true => break LoopLabel1;  // fine
              }
            } else if (m % 101 == 0) {
              break break;  // error: break out of non-ghost loop from ghost context
            }
            m := m + 3;
          }
          break;
        } else if (dontKnow == 708) {
          var q := 0;
          while (q < 1) {
            label IfNest:
            if (p == 67) {
              break break;  // fine, since this is not a ghost context
            } else if (*) {
              break break;  // fine, since this is not a ghost context
            } else if (k == 67) {
              break break;  // error, because this is a ghost context
            }
            q := q + 1;
          }
        } else if (n == t) {
          return;  // error: this is a ghost context trying to return from a non-ghost method
        }
        n := n + 1;
        p := p + 1;
      }
    }
  }
} // HereAreMoreGhostTests

module MiscMore {
  method DuplicateLabels(n: int) {
    var x;
    if (n < 7) {
      label DuplicateLabel: x := x + 1;
    } else {
      label DuplicateLabel: x := x + 1;
    }
    label DuplicateLabel: x := x + 1;
    label DuplicateLabel': {
      label AnotherLabel:
      label DuplicateLabel':  // error: duplicate label (shadowed by enclosing label)
      label OneMoreTime:
      x := x + 1;
    }
    label DuplicateLabel'':
    label DuplicateLabel'':  // error: duplicate label (shadowed by enclosing label)
    x := x + 1;
    label DuplicateLabel'': x := x + 1;  // error: duplicate label (shadowed by dominating label)
  }

  // --------------- constructors -------------------------------------

  class ClassWithConstructor {
    var y: int;
    method NotTheOne() { }
    constructor InitA() { }
    constructor InitB() modifies this; { y := 20; }  // error: don't use "this" in modifies of constructor
  }

  class ClassWithoutConstructor {
    method Init() modifies this; { }
  }

  method ConstructorTests()
  {
    var o := new object;  // fine: does not have any constructors

    o := new ClassWithoutConstructor;  // fine: don't need to call anything particular method
    o := new ClassWithoutConstructor.Init();  // this is also fine

    var c := new ClassWithConstructor.InitA();
    c := new ClassWithConstructor;  // error: must call a constructor
    c := new ClassWithConstructor.NotTheOne();  // error: must call a constructor, not an arbitrary method
    c := new ClassWithConstructor.InitB();
    c.InitB();  // error: not allowed to call constructors except during allocation
  }

  // ------------------- datatype destructors ---------------------------------------

  datatype DTD_List = DTD_Nil | DTD_Cons(Car: int, Cdr: DTD_List, ghost g: int)

  method DatatypeDestructors(d: DTD_List) {
    if {
      case d.DTD_Nil? =>
        assert d == DTD_Nil;
      case d.DTD_Cons? =>
        var hd := d.Car;
        var tl := d.Cdr;
        assert hd == d.Cdr;  // type error
        assert tl == d.Car;  // type error
        assert d.DTD_Cons? == d.Car;  // type error
        assert d == DTD_Cons(hd, tl, 5);
        ghost var g0 := d.g;  // fine
    }
  }
} // MiscMore

// ------------------- print statements ---------------------------------------

module GhostPrintAttempts {
  method PrintOnlyNonGhosts(a: int, ghost b: int)
  {
    print "a: ", a, "\n";
    print "b: ", b, "\n";  // error: print statement cannot take ghosts
  }
}

// ------------------- auto-added type arguments ------------------------------

module MiscEvenMore {
  class GenericClass<T> { var data: T; }

  method MG0(a: GenericClass, b: GenericClass)
    requires a != null && b != null;
    modifies a;
  {
    a.data := b.data;  // allowed, since both a and b get the same auto type argument
  }

  method G_Caller()
  {
    var x := new GenericClass;
    MG0(x, x);  // fine
    var y := new GenericClass;
    MG0(x, y);  // also fine (and now y's type argument is constrained to be that of x's)
    var z := new GenericClass<int>;
    var w := new GenericClass<bool>;
    MG0(x, w);  // this has the effect of making x's and y's type GenericClass<bool>

    y.data := z.data;  // error: bool vs int
    assert x.data == 5;  // error: bool vs int
  }

  datatype GList<+T> = GNil | GCons(hd: T, tl: GList)

  method MG1(l: GList, n: nat)
  {
    if (n != 0) {
      MG1(l, n-1);
      MG1(GCons(12, GCons(20, GNil)), n-1);
    }
    var t := GCons(100, GNil);  // error: types don't match up (List<_T0> versus List<int>)
    t := GCons(120, l);  // error: types don't match up (List<_T0> versus List<int>)
  }

  // ------------------- calc statements ------------------------------

  method TestCalc(m: int, n: int, a: bool, b: bool)
  {
    calc {
      a + b; // error: invalid line
      n + m;
    }
    calc {
      a && b;
      n + m; // error: all lines must have the same type
    }
    calc ==> {
      n + m; // error: ==> operator requires boolean lines
      n + m + 1;
      n + m + 2;
    }
    calc {
      n + m;
      n + m + 1;
      ==> n + m + 2; // error: ==> operator requires boolean lines
    }
  }
} // MiscEvenMore

module MyOwnModule {
  class SideEffectChecks {
    ghost var ycalc: int;

    ghost method Mod(a: int)
      modifies this;
      ensures ycalc == a;
    {
      ycalc := a;
    }

    ghost method Bad()
      modifies this;
      ensures 0 == 1;
    {
      var x: int;
      calc {
        0;
        { Mod(0); }     // error: methods with side-effects are not allowed
        ycalc;
        { ycalc := 1; } // error: heap updates are not allowed
        1;
        { x := 1; }     // error: updates to locals defined outside of the hint are not allowed
        x;
        {
          var x: int;
          x := 1;       // this is OK
        }
        1;
      }
    }
  }
}

// ------------------- nameless constructors ------------------------------

module MiscAgain {
  class Y {
    var data: int;
    constructor (x: int)
    {
      data := x;
    }
    constructor (y: bool)  // error: duplicate constructor name
    {
    }
    method Test() {
      var i := new Y(5);
      i := new Y._ctor(7);  // but, in fact, it is also possible to use the underlying name
      i := new Y;  // error: the class has a constructor, so one must be used
      var s := new Luci.Init(5);
      s := new Luci.FromArray(null);
      s := new Luci(false);
      s := new Luci._ctor(false);
      s := new Luci.M();  // error: there is a constructor, so one must be called
      s := new Luci;  // error: there is a constructor, so one must be called
      var l := new Lamb;
      l := new Lamb();  // error: there is no default constructor
      l := new Lamb.Gwen();
    }
  }

  class Luci {
    constructor Init(y: int) { }
    constructor (nameless: bool) { }
    constructor FromArray(a: array<int>) { }
    method M() { }
  }

  class Lamb {
    method Jess() { }
    method Gwen() { }
  }

  // ------------------- assign-such-that and ghosts ------------------------------

  method AssignSuchThatFromGhost()
  {
    var x: int;
    ghost var g: int;

    x := *;
    assume x == g;  // this mix of ghosts and non-ghosts is cool (but, of course,
                    // the compiler will complain)

    x :| assume x == g;  // this is cool, since it's an assume (but, of course, the
                         // compiler will complain)

    x :| x == 5;
    g :| g <= g;
    g :| assume g < g;  // the compiler will complain here, despite the LHS being
                        // ghost -- and rightly so, since an assume is used
  }
}  // MiscAgain

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

  function FTree0(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => x
  }

  function FTree1(t: Tree): Tree
  {
    match t
    case Leaf(_,_) => t
    case Node(x, y) => y  // error: y does not have the right type
  }

  function FTree2<A,B,C>(t: Tree): Tree<A,B>
  {
    t
  }
}

module NoTypeArgs1 {
  datatype Tree<A,B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

  function FTree3<T>(t: Tree): Tree<T,T>  // error: type of 't' does not have enough type parameters
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
  predicate P<T>(x: T)

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

// ------------ Here are some tests that ghost contexts don't allocate objects -------------

module GhostAllocationTests {
  class G { }
  iterator GIter() { }

  ghost method GhostNew0()
    ensures exists o: G :: fresh(o);
  {
    var p := new G;  // error: ghost context is not allowed to allocate state
    p := new G;  // error: ditto
  }

  method GhostNew1(n: nat, ghost g: int) returns (t: G, z: int)
  {
    if n < 0 {
      z, t := 5, new G;  // fine
    }
    if n < g {
      var zz, tt := 5, new G;  // error: 'new' not allowed in ghost contexts
    }
  }

  method GhostNew2(ghost b: bool)
  {
    if (b) {
      var y := new GIter();  // error: 'new' not allowed in ghost contexts (and a non-ghost method is not allowed to be called here either)
    }
  }

  method GhostNew3(n: nat)
  {
    var g := new G;
    calc {
      5;
      { var y := new G; }  // error: 'new' not allowed in ghost contexts
      2 + 3;
    }
  }

  ghost method GhostNew4(g: G)
    modifies g;
  {
  }
}

module NewForall {
  class G { }
  method NewForallTest(n: nat)
  {
    var a := new G[n];
    forall i | 0 <= i < n {
      a[i] := new G;  // error: 'new' is currently not supported in forall statements
    }
    forall i | 0 <= i < n
      ensures true;  // this makes the whole 'forall' statement into a ghost statement
    {
      a[i] := new G;  // error: 'new' not allowed in ghost contexts, and proof-forall cannot update state
    }
  }
}

// ------------------------- underspecified types ------------------------------

module UnderspecifiedTypes {
  method M(S: set<int>) {
    var n, p, T0 :| 12 <= n && n in T0 && 10 <= p && p in T0 && T0 <= S && p % 2 != n % 2;
    var T1 :| 12 in T1 && T1 <= S;
    var T2 :| T2 <= S && 12 in T2;
    var T3 :| 120 in T3;  // error: underspecified type
    var T3'0: set<int> :| 120 in T3'0;
    var T3'1: multiset<int> :| 120 in T3'1;
    var T3'2: map<int,bool> :| 120 in T3'2;
    var T3'3: seq<int> :| 120 in T3'3;
    var T3'4: bool :| 120 in T3'4;  // error: second argument to 'in' cannot be bool
    var T4 :| T4 <= S;
  }
}

// ------------------------- lemmas ------------------------------
module MiscLemma {
  class L { }

  // a lemma is allowed to have out-parameters, but not a modifies clause
  lemma MyLemma(x: int, l: L) returns (y: int)
    requires 0 <= x;
    modifies l;
    ensures 0 <= y;
  {
    y := x;
  }
}

// ------------------------- statements in expressions ------------------------------

module StatementsInExpressions {
  class MyClass {
    ghost method SideEffect()
      modifies this;
    {
    }

    method NonGhostMethod()
    {
    }

    function F(): int
    {
      calc {
        6;
        { assert 6 < 8; }
        { var x := 8;
          while x != 0
            decreases *  // error: cannot use 'decreases *' here
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
        { var x := 8;
          while x != 0
          {
            x := x - 1;
          }
        }
        6;
      }
      5
    }

    var MyField: int;
    ghost var MyGhostField: int;

    method N()
    {
      var y :=
      calc {
        6;
        { assert 6 < 8; }
        { var x := 8;
          while x != 0
            decreases *  // error: cannot use 'decreases *' here
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

    ghost method MyLemma()
    ghost method MyGhostMethod()
      modifies this;
    method OrdinaryMethod()
    ghost method OutParamMethod() returns (y: int)

    function UseLemma(): int
    {
      MyLemma();
      MyGhostMethod();   // error: modifi2es state
      OutParamMethod();  // error: has out-parameters
      10
    }
  }
}

module GhostLetExpr {
  method M() {
    ghost var y;
    var x;
    var g := G(x, y);
    ghost var h := ghost var ta := F(); 5;
    var j; j := var tb := F(); 5;  // tb is ghost, j is not
    assert h == j;
  }

  function F(): int
  { 5 }

  function method G(x: int, ghost y: int): int
  {
    assert y == x;
    y  // error: not allowed in non-ghost context
  }

  datatype Dt = MyRecord(a: int, ghost b: int)

  method P(dt: Dt) {
    match dt {
      case MyRecord(aa, bb) =>
        ghost var z := aa + F();
        ghost var t0 := var y := z; z + 3;
        ghost var t1 := ghost var y := z + bb; y + z + 3;
        var t2; t2 := ghost var y := z; y + 3;  // t2 is not ghost - error
    }
  }

  function method FM(e: bool): int
  {
    if e then
      G(5, F())
    else
      var xyz := F();  // error: 'xyz' needs to be declared ghost to allow this
      G(5, xyz)
  }
}

module ObjectType {
  type B
  datatype Dt = Blue | Green
  codatatype CoDt = Cons(int, CoDt)
  class MyClass { }

  method M<G>(zz: array<B>, j: int, b: B, co: CoDt, g: G) returns (o: object)
    requires zz != null && 0 <= j < zz.Length;
  {
    o := b;  // error
    o := 17;  // error
    o := zz[j];  // error
    o := null;
    o := zz;
    o := new MyClass;
    o := o;
    o := g;  // error
    o := Blue;  // error
    o := co;  // error
  }
}

// ------------------ modify statment ---------------------------

module MiscModify {
  class ModifyStatementClass {
    var x: int;
    ghost var g: int;
    method M()
    {
      modify x;  // error: type error
    }
    ghost method G0()
      modifies `g;
      modifies `x;  // error: non-ghost field mentioned in ghost context
  }
}

module ModifyStatementClass_More {
  class C {
    var x: int;
    ghost var g: int;
    ghost method G0()
      modifies `g;
    {
      modify `g;
      modify `x;  // error: non-ghost field mentioned in ghost context
    }
    method G1()
      modifies this;
    {
      modify `x;
      if g < 100 {
        // we are now in a ghost context
        modify `x;  // error: non-ghost field mentioned in ghost context
      }
    }
    method G2(y: nat)
      modifies this;
    {
      if g < 100 {
        // we're now in a ghost context
        var n := 0;
        while n < y
          modifies `x;  // error: non-ghost field mentioned in ghost context
        {
          if * {
            g := g + 1;  // if we got as far as verification, this would be flagged as an error too
          }
          n := n + 1;
        }
      }
      modify `x;  // fine
      ghost var i := 0;
      while i < y
        modifies `x;  // error: non-ghost field mentioned in ghost context
      {
        i := i + 1;
      }
    }
  }
}

module LhsLvalue {
  method M()
  {
    var mySeq: seq<int>;
    var a := new int[78];
    var b := new int[100, 200];
    var c := new MyRecord[29];

    mySeq[0] := 5;  // error: cannot assign to a sequence element
    mySeq[0] := MyLemma();  // error: ditto
    a[0] := 5;
    a[0] := MyLemma();
    b[20, 18] := 5;
    b[20, 18] := MyLemma();
    c[25].x := 5;  // error: cannot assign to a destructor
    c[25].x := MyLemma();  // error: ditto
    mySeq[0..4] := 5;  // error: cannot assign to a range
    mySeq[0..4] := MyLemma();  // error: ditto
    a[0..4] := 5;  // error: cannot assign to a range
    a[0..4] := MyLemma();  // error: ditto
  }

  datatype MyRecord = Make(x: int, y: int)

  method MyLemma() returns (w: int)
}

// ------------------- dirty loops -------------------
module MiscEtc {
  method DirtyM(S: set<int>) {
    forall s | s in S ensures s < 0;
    assert s < 0; // error: s is unresolved
  }

  // ------------------- tuples -------------------

  method TupleResolution(x: int, y: int, r: real)
  {
    var unit: () := ();
    var expr: int := (x);
    var pair: (int,int) := (x, x);
    var triple: (int,int,int) := (y, x, x);
    var badTriple: (int,real,int) := (y, x, r);  // error: parameters 1 and 2 have the wrong types
    var quadruple: (int,real,int,real) := (y, r, x);  // error: trying to use a triple as a quadruple

    assert unit == ();
    assert pair.0 == pair.1;
    assert triple.2 == x;

    assert triple.2;  // error: 2 has type int, not the expected bool
    assert triple.3 == pair.x;  // error(s):  3 and x are not destructors

    var k0 := (5, (true, 2, 3.14));
    var k1 := (((false, 10, 2.7)), 100, 120);
    if k0.1 == k1.0 {
      assert false;
    } else if k0.1.1 < k1.0.1 {
      assert k1.2 == 120;
    }

    // int and (int) are the same type (i.e., there are no 1-tuples)
    var pp: (int) := x;
    var qq: int := pp;
  }

  // ------------------- conversions -------------------

  method TypeConversions(m: nat, i: int, r: real) returns (n: nat, j: int, s: real)
  {
    n := r as int;
    j := r as int;
    s := m as real;  // nat->real is allowed, just like int->real is
    s := i as real;
    s := i as real / 2;  // error: division expects two reals
    s := 15 % s;  // error: modulus is not defined for reals

    s := (2.0 / 1.7) + (r / s) - (--r) * -12.3;

    s := s as real;  // fine (identity transform)
    j := j as int;  // fine (identity transform)
    j := n as int;  // fine (identity transform)
  }
}

// --- filling in type arguments and checking that there aren't too many ---

module TypeArgumentCount {
  class C<T> {
    var f: T;
  }

  method R0(a: array3, c: C)

  method R1()
  {
    var a: array3;
    var c: C;
  }

  method R2<T>()
  {
    var a: array3<T,int>;  // error: too many type arguments
    var c: C<T,int>;  // error: too many type arguments
  }
}

// --- Type synonyms ---

module BadTypeSynonyms {
  datatype List<T> = Nil | Cons(T, List)
  type BadSyn0 = List  // error: must have at least one type parameter
  type BadSyn1 = badName  // error: badName does not denote a type
  type BadSyn2 = List<X>  // error: X does not denote a type
  type BadSyn2 = int  // error: repeated name
}

// --- cycles ---

module CycleError0 {
  type A = A  // error: cycle: A -> A
}
module CycleError1 {
  type A = B  // error: cycle: A -> B -> A
  type B = A
}
module CycleError2 {
  type A = B  // error: cycle: A -> B -> A
  type B = set<A>
}
module CycleErrors3 {
  type A = (B, D<bool>)
  type B = C
  class C {
    var a: A;  // this is fine
  }
  datatype D<X> = Make(A, B, C)  // error: cannot construct a D<X>
}
module CycleError4 {
  type A = B  // error: cycle: A -> B -> A
  type B = C<A>
  class C<T> { }
}
module CycleError5 {
  type A = B  // error: cycle: A -> B -> A
  type B = Dt<A>
  datatype Dt<T> = Make(T)
}
module CycleError6 {
  type A = Dt<Dt<A>>  // error: cycle A -> Dt<Dt<A>> -> Dt<A> -> A
  datatype Dt<T> = Make(T)
}

// --- attributes in top-level declarations ---

module MiscIterator {
  iterator {:myAttribute x} Iter() {  // error: x does not refer to anything
  }

  class {:myAttribute x} C {  // error: x does not refer to anything
  }

  datatype {:myAttribute x} Dt = Blue  // error: x does not refer to anything

  type {:myAttribute x} Something  // error: x does not refer to anything

  type {:myAttribute x} Synonym = int  // error: x does not refer to anything
}

module {:myAttribute x} Modulette {  // error: x does not refer to anything
}

// --- opaque types with type parameters ---

module OpaqueTypes0 {
  type P<AA>
  method M<B>(p: P<B>) returns (q: P<B,B>)  // error: wrong param count
  {
    q := p;
  }
}

module OpaqueTypes1 {
  type P<A>

  method M0<B>(p: P<B>) returns (q: P<B>)
  {
    q := p;
    var m: P<BX>;  // error: BX undefined
  }

  method M1<B>(p: P<B>) returns (q: P)  // type parameter of q's type inferred
  {
    q := p;
  }

  method M2(p: P<int>) returns (q: P<bool>)
  {
    q := p;  // error: cannot assign P<bool> to P<int>
  }

  method M3<A,B>(p: P<A>) returns (q: P<B>)
  {
    q := p;  // error: cannot assign P<A> to P<B>
  }

  method M4<A>() returns (p: P<A>, q: P<int>)
  {
    q := p;  // error: cannot assign P<A> to P<int>
    p := q;  // error: cannot assign P<int> to P<A>
  }

  method EqualityTests<X>(p: P<int>, q: P<bool>, r: P<X>)
  {
    assert p != r;  // error: types must be the same in order to do compare
    assert q != r;  // error: types must be the same in order to do compare
    assert p != q;  // error: types must be the same in order to do compare
  }
}

// ----- new trait -------------------------------------------

module MiscTrait {
  trait J { }
  type JJ = J
  method TraitSynonym()
  {
    var x := new JJ;  // error: new cannot be applied to a trait
  }
}

// ----- set comprehensions where the term type is finite -----

module ObjectSetComprehensions {
  // the following set comprehensions are known to be finite
  function A() : set<object> { set o : object | true :: o }  // error: a function is not allowed to depend on the allocated state

  function method B() : set<object> { set o : object | true :: o }  // error: a function is not allowed to depend on the allocated state

  // outside functions, the comprehension is permitted, but it cannot be compiled
  lemma C() { var x; x := set o : object | true :: o; }

  method D() { var x; x := set o : object | true :: o; }  // error: not (easily) compilable
}

// ------ regression test for type checking of integer division -----

module MiscTests {
  method IntegerDivision(s: set<bool>)
  {
    var t := s / s;  // error: / cannot be used with sets
  }

  // ----- decreases * tests ----

  method NonTermination_A()
  {
    NonTermination_B();  // error: to call a non-terminating method, the caller must be marked 'decreases *'
  }

  method NonTermination_B()
    decreases *;
  {
    while true
      decreases *;
    {
    }
  }

  method NonTermination_C()
  {
    while true
      decreases *;  // error: to use an infinite loop, the enclosing method must be marked 'decreases *'
    {
    }
  }

  method NonTermination_D()
    decreases *;
  {
    var n := 0;
    while n < 100  // note, no 'decreases *' here, even if the nested loop may fail to terminate
    {
      while *
        decreases *;
      {
      }
      n := n + 1;
    }
  }
}

// ------------ type variables whose values are not inferred ----------

module NonInferredTypeVariables {
  class C<CT> {
    var f: CT;
  }

  predicate method P<PT>(x: int)
  {
    x < 100
  }
  function Q<QT>(x: int): QT
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
    var b0 := forall s :: s <= {} ==> s == {};  // error: type of s underspecified
    var b1 := forall s: set :: s <= {} ==> s == {};  // error: type of s underspecified
    var b2 := forall c: C? :: c in {null} ==> c == null;  // error: type parameter of c underspecified

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

  function F0<A,B>(s: set, x: A -> B): int
  function F1<A,B>(x: A -> B, s: set): int
  function F2<A,B>(s: set, x: A -> B): int
  function F3<A,B>(x: A -> B, s: set): int
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
      predicate Q()
    }
  }
  module B {
    module Inner {
      predicate Q()
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
    assert X == X;  // error (x2): type name used as variable
    assert Y == Y;  // error (x2): module name used as variable
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
  function F(): int {
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
    modifies g;
  {
  }

  class MyClass {
    ghost method SideEffect()
      modifies this;
    {
    }

    method NonGhostMethod()
    {
    }

    ghost method M()
      modifies this;
    {
      calc {
        5;
        { SideEffect(); }  // error: cannot call method with side effects
        5;
      }
    }
    function F(): int
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
            modifies this;  // error: cannot use a modifies clause on a loop
          {
            x := x - 1;
          }
        }
        6;
      }
      5
    }
    var MyField: int;
    ghost var MyGhostField: int;
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
            modifies this;  // error: cannot use a modifies clause on a loop
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
    ghost method MyLemma()
    ghost method MyGhostMethod()
      modifies this;
    method OrdinaryMethod()
    ghost method OutParamMethod() returns (y: int)

    function UseLemma(): int
    {
      MyLemma();
      OrdinaryMethod();  // error: not a ghost
      10
    }
  }
}

module EvenMoreGhostTests {
  ghost method NiceTry()
    ensures false;
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
  function method P<T>(x: T): int
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

// ------------------- infer array types for Indexable and MultiIndexable XConstraints ----------
// ------------------- using weaker subtyping constraints                              ----------

module AdvancedIndexableInference {
  datatype MyRecord = Make(x: int, y: int)
  method M(d: array<MyRecord>, e: seq<MyRecord>)
    requires d.Length == 100 == |e|
  {
    if * {
      var c := d;
      var xx := c[25].x;
    } else if * {
      var c := d;
      var xx := c[25..50][10].x;
    } else if * {
      var c := e;
      var xx := c[25].x;
    } else {
      var c := e;
      var xx := c[25..50][10].x;
    }
  }
}

// --------------------------

module TypeConversions {
  trait J { }
  class C extends J { }
  method M() returns (x: int, n: nat, o: object, j: J, c: C) {
    n := x as nat;  // yes, this is allowed now
    o := j;
    j := o;  // error: cannot assign 'object' to 'J'
    j := o as J;  // error: not allowed to convert to 'J'
    j := c;
    c := j;  // error: cannot assign J' to 'C'
    c := j as C;  // error: not allowed to convert to 'C'
    var oo := o as realint;  // error: there's no such type as "realint" (this once used to crash Dafny)
  }
}

// --------------------- regression

module Regression_NewType {
  class C { }
  newtype MyInt = x: int | {} == set c: C | c  // this once crashed Dafny
}

// --------------------- regression

module PrefixGeneratorDuplicates {
  copredicate P()
  copredicate P()  // error: duplicate name (this once crashed Dafny)
  colemma L()
  colemma L()  // error: duplicate name (this once crashed Dafny)
}

// ------------------- unary TLA+ style predicates -------------------

module TLAplusOperators {
  function BadA(y: int): int  // error: body has wrong return type
  {
    && 5 + y  // error: using operator "&&" requires the operand to be boolean
  }
  function BadB(y: int): bool
  {
    && 5 + y  // error: using operator "&&" requires the operand to be boolean
  }
  function BadC(y: int): int  // error: body has wrong return type
  {
    || 5 + y  // error: using operator "||" requires the operand to be boolean
  }
  function BadD(y: int): bool
  {
    || 5 + y  // error: using operator "||" requires the operand to be boolean
  }
  function BadE(y: int): int  // error: body has wrong return type
  {
    && (|| 5 + y)  // error: bad types
  }
}

// ------------------------- divided constructors -------------------

module DividedConstructors {

  class MyClass {
    var a: nat
    var b: nat
    var c: nat
    var n: MyClass
    const t := 17
    static const g := 25

    constructor Init(x: nat)
    {
      this.a := this.b;  // this use of "this" in RHS is allowed
      ((this)).b := 10;
      n := new MyClass();
      n.a := 10;  // error: not allowed use of "this" in this way
      c := a + b;  // error (x2): not allowed "this" in RHS
      var th := this;  // error: not allowed "this" in RHS
      Helper();  // error: not allowed to call instance method
      var mc := new MyClass();
      StaticHelper(mc);
      this.StaticHelper(mc);  // "this" is benign here
      StaticHelper(this);  // error: cannot use "this" here
      P(a);  // error: cannot use "this" here
      P(g);
      P(this.g);  // "this" is benign here
      modify this;  // error: cannot use "this" here
      modify this`c;  // error: cannot use "this" here
      modify `c;  // error: cannot use (implicit) "this" here
      new;
      a := a + b;
      Helper();
    }

    method Helper()
    {
    }

    static method StaticHelper(mc: MyClass)
    {
    }

    static method P(x: nat)
    {
    }

    constructor ()
    {
      a, c := 0, 0;
      new;
    }

  }
}

module ConstructorsThisUsage {
  class C {
    var x: int
    constructor M()
      requires this != null  // error: cannot use "this" here
      modifies this  // error: cannot use "this" here (but we just issue a deprecation warning)
      decreases this.x  // error: cannot use "this" here
      ensures this.x == 5
    {
      x := 5;
    }
  }
}

module ReturnBeforeNew {
  class C {
    var a: int
    var b: int
    constructor TriesToReturnBeforeNew(xyz: int)
    {
      a := 0;
      if xyz < 100 {
        return;  // error: "return" is not allowed before "new;"
      }
    }
  }
}

// ---------------- required zero initialization -----------------------

module ZI {
  // the following are different syntactic ways of saying that the type
  // must support zero initialization
  type ZA(0)
  type ZB(==)(0)
  type ZC(0)(==)
  type ZD(==,0)
  type ZE(0,==)
  type Y

  method P<G(0)>(x: G)
  method M0<F,G(0)>(a: ZA, b: ZB, c: ZC, d: ZD, e: ZE, f: F, g: G, y: Y)
  {
    P(a);
    P(b);
    P(c);
    P(d);
    P(e);
    P(f);  // error: type of argument is expected to support zero initialization
    P(g);
    P(y);  // error: type of argument is expected to support zero initialization
  }

  datatype List<T> = Nil | Cons(T, List<T>)
  method M1<G,H(0)>(xs: List<G>, ys: List<H>) {
    P(xs);  // yay, type of argument does support zero initialization
    P(ys);  // yay, type of argument does support zero initialization
  }

  class Cls {
    var q: int
    var rs: List<List<Cls>>
  }
  method M2(c: Cls?) {
    P(c);
  }

  newtype byte = x: int | 0 <= x < 256  // supports zero initialization
  newtype MyInt = int  // supports zero initialization
  newtype SixOrMore = x | 6 <= x witness 6
  newtype AnotherSixOrMore = s: SixOrMore | true witness 6
  newtype MySixOrMore = x: MyInt | 6 <= x witness 6
  // The resolver uses the presence/absence of a "witness" clause to figure out if the type
  // supports zero initialization.  This can be inaccurate.  If the type does not have a
  // "witness" clause, some type replacements may slip by the resolver, but will then be
  // caught by the verifier when the witness test is performed (because the witness test
  // uses a zero value in the absence of a "witness" clause).  Regrettably, if a "witness"
  // clause is supplied unnecessarily (perhaps to be explicit about the witness in the
  // program text), then the resolver will treat the type as if it does not support
  // zero initialization, and hence some good programs will be rejected by the resolver.
  newtype UnclearA = x: int | true witness 0  // actually supports zero initialization, but has a "witness" clause
  newtype UnclearB = x | 6 <= x  // "witness" clause omitted; type does not actually support zero initialization

  method M3(a: byte, b: MyInt, c: SixOrMore, d: AnotherSixOrMore, e: MySixOrMore,
            ua: UnclearA, ub: UnclearB) {
    P(a);
    P(b);
    P(c);  // error: type of argument is expected to support zero initialization
    P(d);  // error: type of argument is expected to support zero initialization
    P(e);  // error: type of argument is expected to support zero initialization
    P(ua);  // error: as far as the resolver can tell, type of argument does not support zero initialization
    P(ub);  // fine, as far as the resolver can tell (but this would be caught later by the verifier)
  }

  type Sbyte = x: int | 0 <= x < 256  // supports zero initialization
  type SMyInt = int  // supports zero initialization
  type SSixOrMore = x | 6 <= x witness 6
  type SAnotherSixOrMore = s: SSixOrMore | true witness 6
  type SMySixOrMore = x: SMyInt | 6 <= x witness 6
  type SUnclearA = x: int | true witness 0  // see note about for UnclearA
  type SUnclearB = x | 6 <= x  // see note about for UnclearB

  method M4(a: Sbyte, b: SMyInt, c: SSixOrMore, d: SAnotherSixOrMore, e: SMySixOrMore,
            sua: SUnclearA, sub: SUnclearB) {
    P<Sbyte>(a);
    P<SMyInt>(b);
    P<SSixOrMore>(c);  // error: type of argument is expected to support zero initialization
    P<SAnotherSixOrMore>(d);  // error: type of argument is expected to support zero initialization
    P<SMySixOrMore>(e);  // error: type of argument is expected to support zero initialization
    P<SUnclearA>(sua);  // error: as far as the resolver can tell, type of argument does not support zero initialization
    P<SUnclearB>(sub);  // fine, as far as the resolver can tell (but this would be caught later by the verifier)
  }
}

abstract module ZI_RefinementAbstract {
  type A
  type A'
  type B(0)
  type B'(0)

  type Mxx(0)
  type Mx_
  type M_x(0)
  type M__

  method Delta<Q(0),W,E(0),R>()
}

module ZI_RefinementConcrete0 refines ZI_RefinementAbstract {
  newtype Six = x | 6 <= x witness 6  // does not support zero initialization
  type A = int
  type A' = Six
  type B = int
  type B' = Six  // error: RHS is expected to support zero initialization
}

module ZI_ExportSource {
  export
    reveals RGB
    provides XYZ
  datatype RGB = Red | Green | Blue
  datatype XYZ = X | Y | Z
}

module ZI_RefinementConcrete1 refines ZI_RefinementAbstract {
  import Z = ZI_ExportSource

  method P<G(0)>(g: G)
  method M(m: Z.RGB, n: Z.XYZ) {
    P(m);
    P(n);  // error: Z.XYZ is not known to support zero initialization
  }

  type Mxx  // error: not allowed to change zero-initialization setting
  type Mx_
  type M_x(0)
  type M__(0)  // error: not allowed to change zero-initialization setting

  method Delta<
    Q,  // error: not allowed to change zero-initialization setting
    W,
    E(0),
    R(0)>()  // error: not allowed to change zero-initialization setting
}

// ----- constructor-less classes with need for initialization -----

module ConstructorlessClasses {
  class C<T(==)> {  // error: must have constructor
    var x: int
    var s: string
    var t: set<T>
    var u: T
    const c: T
  }

  method Test()
  {
    var c := new C<set<real>>;
    print "int: ", c.x, "\n";
    print "string: ", c.s, "\n";
    print "set<set<real>>: ", c.t, "\n";
    print "real: ", c.u, "\n";
    print "real: ", c.c, "\n";
  }

  codatatype Co = CoEnd | Suc(Co)

  trait Trait {
    var co: Co  // has no known initializer
  }
  class Class extends Trait {  // error: must have constructor, because of inherited field "co"
  }

  class CoClass0 {  // error: must have constructor
    const co: Co
  }

  class CoClass1 {  // fine
    const co: Co := CoEnd
  }

  trait CoTrait {
    const co: Co := CoEnd
  }
  class CoClass2 extends CoTrait {  // fine
  }

  iterator Iter<T>(u: T) yields (v: T)
  {
  }
}

module GhostWitness {
  type BadGhost_EffectlessArrow<A,B> = f: A -> B
    | true
    witness (GhostEffectlessArrowWitness<A,B>)  // error: a ghost witness must use the keyword "ghost"

  type GoodGhost_EffectlessArrow<A,B> = f: A -> B
    | true
    ghost witness (GhostEffectlessArrowWitness<A,B>)

  function GhostEffectlessArrowWitness<A,B>(a: A): B
  {
    var b: B :| true; b
  }
}

module BigOrdinalRestrictions {  // also see BigOrdinalRestrictionsExtremePred below
  method Test() {
    var st: set<ORDINAL>;  // error: cannot use ORDINAL as type argument
    var p: (int, ORDINAL);  // error: cannot use ORDINAL as type argument
    var o: ORDINAL;  // okay
    ghost var f := F(o);  // error: cannot use ORDINAL as type argument
    f := F'<ORDINAL>();  // error: cannot use ORDINAL as type argument
    f := F'<(char,ORDINAL)>();  // error: cannot use ORDINAL as type argument
    var lambda := F'<ORDINAL>;  // error: cannot use ORDINAL as type argument
    ParameterizedMethod(o);  // error: cannot use ORDINAL as type argument
    assert forall r: ORDINAL :: P(r);
    assert forall r: (ORDINAL, int) :: F(r.1) < 8;
    assert exists x: int, r: ORDINAL, y: char :: P(r) && F(x) == F(y);
    var s := set r: ORDINAL | r in {};  // error: cannot use ORDINAL as type argument (to set)
    var s' := set r: ORDINAL | true :: 'G';
    ghost var m := imap r: ORDINAL :: 10;
    var sq := [o, o];  // error: cannot use ORDINAL as type argument (to seq)
    var mp0 := map[o := 'G'];  // error: cannot use ORDINAL as type argument (to map)
    var mp1 := map['G' := o];  // error: cannot use ORDINAL as type argument (to map)
    var w := var h: ORDINAL := 100; h + 40;  // okay
    var w': (int, ORDINAL);  // error: cannot use ORDINAL as type argument
    var u: ORDINAL :| u == 15;
    var ti: ORDINAL :| assume true;
    var u': (ORDINAL, int) :| u' == (15, 15);  // error (x2): ORDINAL cannot be a type argument
    var ti': (ORDINAL, ORDINAL) :| assume true;  // error (x4): ORDINAL cannot be a type argument
    var lstLocal := var lst: ORDINAL :| lst == 15; lst;
    var lstLocal' := var lst: (ORDINAL, int) :| lst == (15, 15); lst.1;  // error: ORDINAL cannot be a type argument
    if yt: ORDINAL :| yt == 16 {
      ghost var pg := P(yt);
    }
    if {
      case zt: ORDINAL :| zt == 180 =>
        ghost var pg := P(zt);
    }
    forall om: ORDINAL  // allowed
      ensures om < om+1
    {
    }
    var arr := new int[23];
    forall om: ORDINAL | om == 11  // allowed
    {
      arr[0] := 0;
    }
  }
  function F<G>(g: G): int
  function F'<G>(): int
  method ParameterizedMethod<G>(g: G)
  predicate P(g: ORDINAL)
}

module IteratorDuplicateParameterNames {
  // each of the following once caused a crash in the resolver
  iterator MyIterX(u: char) yields (u: char)  // error: duplicate name "u"
  iterator MyIterY(us: char) yields (u: char)  // error: in-effect-duplicate name "us"
}

module TernaryTypeCheckinngAndInference {
  codatatype Stream = Cons(int, Stream)

  method M(k: nat, K: ORDINAL, A: Stream, B: Stream)
    requires A == B
  {
    // all of the following are fine
    assert A ==#[k] B;
    assert A ==#[K] B;
    assert A ==#[3] B;
    var b;
    assert A ==#[b] B;
  }
}

module DontQualifyWithNonNullTypeWhenYouMeanAClass {
  module Z {
    class MyClass {
      static const g := 100
    }
    method M0() {
      var x := MyClass?.g;  // error: use MyClass, not MyClass?
      assert x == 100;
    }
    method M1() {
      var x := MyClass.g;  // that's it!
      assert x == 100;
    }
    method P(from: MyClass) returns (to: MyClass?) {
      to := from;
    }
    method Q() {
      var x := MyClass;  // error: type used as variable
      var y := MyClass?;  // error: type used as variable
    }
  }

  module A {
    class MyClass {
      static const g := 100
    }
  }

  module B {
    import A
    method M0() {
      var x := A.MyClass?.g;  // error: use MyClass, not MyClass?
      assert x == 100;
    }
    method M1() {
      var x := A.MyClass.g;  // that's it!
      assert x == 100;
    }
    method P(from: A.MyClass) returns (to: A.MyClass?) {
      to := from;
    }
    method Q() {
      var x := A.MyClass;  // error: type used as variable
      var y := A.MyClass?;  // error: type used as variable
    }
  }
}

module UninterpretedModuleLevelConst {
  type Six = x | 6 <= x witness 6
  type Odd = x | x % 2 == 1 ghost witness 7
  const S: Six  // fine
  const X: Odd  // error: the type of a non-ghost static const must have a known initializer

  class MyClass { }
  const Y: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
  ghost const Y': MyClass  // fine, Y' is ghost

  class AnotherClass {  // fine, the class itself is not required to have a constructor, because the bad fields are static
    static const k := 18
    static const W: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
    static const U: Six  // fine, since Six has a non-ghost witness and thus has a known initializer
    static const O: Odd  // error: the type of a non-ghost static const must have a known initializer
    const u: Six
  }

  trait Trait {
    static const k := 18
    static const W: MyClass  // error: the type of a non-ghost static const must have a known (non-ghost) initializer
    static const U: Six  // fine, since Six has a non-ghost witness and thus has a known initializer
    static const O: Odd  // error: the type of a non-ghost static const must have a known initializer
  }
  class ClassyTrait extends Trait {  // fine, since the bad fields in Trait are static
  }

  trait InstanceConst {
    const w: MyClass
  }
  class Instance extends InstanceConst {  // error: because of "w", must declare a constructor
  }

  trait GhostTr {
    ghost const w: MyClass  // ghost, so no prob
  }
  class GhostCl extends GhostTr {
    ghost const z: MyClass  // ghost, so no prob
  }
}

module NonThisConstAssignments {
  const X: int

  class Cla {
    constructor () {
      X := 15;  // error: can never assign to static const (this used to crash)
      Clb.Y := 15;  // error: can never assign to static const (this used to crash)
    }
  }

  class Clb {
    static const Y: int
    constructor () {
      Y := 15;  // error: cannot ever assign to a static const (this used to crash)
    }
  }

  class Clc {
    const Z: int
    constructor (c: Clc) {
      c.Z := 15;  // error: can assign to const only for 'this' (this used to crash)
    }
  }

  class Cld {
    const Z: int
    constructor () {
      Z := 15;
    }
  }
}

module ConstGhostRhs {
  class S {
    const m: int := n  // error: use of ghost to assign non-ghost field
    ghost const n: int
  }
  const a: int := b  // error: use of ghost to assign non-ghost field
  ghost const b: int

  class S' {
    ghost const m': int := n'
    const n': int
  }
  ghost const a': int := b'
  const b': int

}

module Regression15 {
  predicate method F(i: int, j: int) { true }
  function method S(i: int): set<int> { {i} }
  method M0() returns (b: bool) {
    b := forall i, j | j <= i <= 100 && i <= j < 100 :: true;  // error: this bogus cyclic dependency was once allowed
  }
  method M4() returns (b: bool) {
    b := forall i, j :: j <= i < 100 && j in S(i) ==> F(i,j);  // error: this bogus cyclic dependency was once allowed
  }
}

module AllocDepend0 {
  class Class {
    const z := if {} == set c: Class | true then 5 else 4  // error (x2): condition depends on alloc; not compilable
  }
  const y := if {} == set c: Class | true then 5 else 4  // error (x2): condition depends on alloc; not compilable
  newtype byte = x | x < 5 || {} == set c: Class | true  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || {} == set c: Class | true  // error: condition not allowed to depend on alloc
}
module AllocDepend1 {
  class Class { }
  predicate method P(x: int) {
    x < 5 || {} == set c: Class | true  // error: function not allowed to depend on alloc
  }
}

module AllocDepend2 {
  class Klass {
    const z := if exists k: Klass :: allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  }
  const y := if exists k: Klass :: allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  newtype byte = x | x < 5 || exists k: Klass :: allocated(k)  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || exists k: Klass :: allocated(k)  // error: condition not allowed to depend on alloc
}
module AllocDepend3 {
  class Klass { }
  predicate method P(x: int) {
    x < 5 || exists k: Klass :: allocated(k)  // error: function not allowed to depend on alloc
  }
}

module AllocDepend4 {
  class Xlass {
    const z := if var k: Xlass? := null; allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  }
  const y := if var k: Xlass? := null; allocated(k) then 3 else 4  // error (x2): condition depends on alloc
  newtype byte = x | x < 5 || var k: Xlass? := null; allocated(k)  // error: condition not allowed to depend on alloc
  type small = x | x < 5 || var k: Xlass? := null; allocated(k)  // error: condition not allowed to depend on alloc
}
module AllocDepend5 {
  class Xlass { }
  predicate method P(x: int) {
    x < 5 || var k: Xlass? := null; allocated(k)  // error: function not allowed to depend on alloc
  }
}

module AbstemiousCompliance {
  codatatype EnormousTree<X> = Node(left: EnormousTree, val: X, right: EnormousTree)

  function {:abstemious} Five(): int {
    5  // error: an abstemious function must return with a co-constructor
  }

  function {:abstemious} Id(t: EnormousTree): EnormousTree
  {
    t  // to be abstemious, a parameter is as good as a co-constructor
  }

  function {:abstemious} IdGood(t: EnormousTree): EnormousTree
  {
    match t
    case Node(l, x, r) => Node(l, x, r)
  }

  function {:abstemious} AlsoGood(t: EnormousTree): EnormousTree
  {
    Node(t.left, t.val, t.right)
  }

  function {:abstemious} UniformTree<X>(x: X): EnormousTree<X>
  {
    Node(UniformTree(x), x, UniformTree(x))
  }

  function {:abstemious} AlternatingTree<X>(x: X, y: X): EnormousTree<X>
  {
    Node(AlternatingTree(y, x), x, AlternatingTree(y, x))
  }

  function {:abstemious} AnotherAlternatingTree<X>(x: X, y: X): EnormousTree<X>
  {
    var t := Node(AlternatingTree(x, y), y, AlternatingTree(x, y));
    Node(t, x, t)
  }

  function {:abstemious} NonObvious<X>(x: X): EnormousTree<X>
  {
    AlternatingTree(x, x)  // error: does not return with a co-constructor
  }

  function {:abstemious} BadDestruct(t: EnormousTree): EnormousTree
  {
    Node(t.left, t.val, t.right.right)  // error: cannot destruct t.right
  }

  function {:abstemious} BadMatch(t: EnormousTree): EnormousTree
  {
    match t.right  // error: cannot destruct t.right
    case Node(a, x, b) =>
      Node(a, x, b)
  }

  function {:abstemious} BadEquality(t: EnormousTree, u: EnormousTree, v: EnormousTree): EnormousTree
  {
    if t == u then  // error: cannot co-compare
      Node(t.left, t.val, t.right)
    else if u != v then  // error: cannot co-compare
      Node(u.left, u.val, u.right)
    else
      Node(v.left, v.val, v.right)
  }

  function {:abstemious} Select(b: bool, t: EnormousTree, u: EnormousTree): EnormousTree
  {
    if b then t else u  // abstemious yes: parameters are as good as a co-constructors
  }

  function {:abstemious} Select'(b: bool, t: EnormousTree, u: EnormousTree): EnormousTree
  {
    if b then
      Node(t.left, t.val, t.right)  // fine, too
    else
      Node(u.left, u.val, u.right)  // fine, too
  }
}

module BigOrdinalRestrictionsExtremePred {
  inductive predicate Test() {
    var st: set<ORDINAL> := {};  // error: cannot use ORDINAL as type argument
    var p: (int, ORDINAL) := (0,0);  // error: cannot use ORDINAL as type argument
    var o: ORDINAL := 0;  // okay
    ghost var f := F(o);  // error: cannot use ORDINAL as type argument
    var f := F'<ORDINAL>();  // error: cannot use ORDINAL as type argument
    var f := F'<(char,ORDINAL)>();  // error: cannot use ORDINAL as type argument
    var lambda := F'<ORDINAL>;  // error: cannot use ORDINAL as type argument
    ParameterizedLemma(o);  // error: cannot use ORDINAL as type argument
    assert forall r: ORDINAL :: P(r);  // error: cannot quantify over ORDINAL here
    assert forall r: (ORDINAL, int) :: F(r.1) < 8;  // error: cannot quantify over ORDINAL here
    assert exists x: int, r: ORDINAL, y: char :: P(r) && F(x) == F(y);  // error: cannot quantify over ORDINAL here
    var s := set r: ORDINAL | r in {};  // error (x2): cannot use ORDINAL as type argument (to set)
    var s' := set r: ORDINAL | true :: 'G';  // error: cannot use ORDINAL here
    ghost var m := imap r: ORDINAL :: 10;  // error (x2): cannot use ORDINAL here
    var sq := [o, o];  // error: cannot use ORDINAL as type argument (to seq)
    var mp0 := map[o := 'G'];  // error: cannot use ORDINAL as type argument (to map)
    var mp1 := map['G' := o];  // error: cannot use ORDINAL as type argument (to map)
    var w := var h: ORDINAL := 100; h + 40;  // okay
    var w': (int, ORDINAL) := (8,8);  // error: cannot use ORDINAL as type argument
    var u: ORDINAL :| u == 15;
    var ti: ORDINAL :| true;
    var u': (ORDINAL, int) :| u' == (15, 15);  // error (x2): ORDINAL cannot be a type argument
    var ti': (ORDINAL, ORDINAL) :| true;  // error (x2): ORDINAL cannot be a type argument
    var lstLocal := var lst: ORDINAL :| lst == 15; lst;
    var lstLocal' := var lst: (ORDINAL, int) :| lst == (15, 15); lst.1;  // error: ORDINAL cannot be a type argument
    var gr := if yt: ORDINAL :| yt == 16 then
      ghost var pg := P(yt); 5
    else
      7;
    calc {
      100;
    ==  {
          forall om: ORDINAL  // allowed
            ensures om < om+1
          {
          }
        }
      100;
    }
    true
  }
  function F<G>(g: G): int
  function F'<G>(): int
  lemma ParameterizedLemma<G>(g: G)
  predicate P(g: ORDINAL)
}

// ----- label domination -----

module LabelDomination {
  method DuplicateLabels(n: int) {
    var x;
    if (n < 7) {
      label L: x := x + 1;
    } else {
      label L: x := x + 1;
    }
    assert old@L(true);  // error: L is not available here
    label L: x := x + 1;
    assert old@L(true);
    label L: x := x + 1;  // error: duplicate label
    assert old@L(true);

    {
      label K:
      x := x + 1;
    }
    assert old@K(true);
    label K:  // error: duplicate label
    assert old@K(true);
  }

  datatype Color = A | B | C
  method Branches(n: int, c: Color) {
    var x: int;
    if n < 2 {
      label X: x := x + 1;
    } else if n < 4 {
      label X: x := x + 1;
    } else {
      label X: x := x + 1;
    }
    if * {
      label X: x := x + 1;
    } else {
      label X: x := x + 1;
    }

    if {
      case true =>
        label X: x := x + 1;
      case true =>
        label X: x := x + 1;
    }

    var i := 0;
    while i < x {
      label X: x := x + 1;
      i := i + 1;
    }

    i := 0;
    while {
      case i < x =>
        label X: x := x + 1;
        i := i + 1;
      case i < x =>
        label X: x := x + 1;
        i := i + 1;
    }

    match c {
      case A =>
        label X: x := x + 1;
      case B =>
        label X: x := x + 1;
      case C =>
        label X: x := x + 1;
    }

    label X: x := x + 1;  // all okay
  }

  method A0() {
    label Q:
    assert true;
  }
  method A1() {
    label Q:
    assert true;
  }

  class MyClass {
    var x: int
    method LabelNotInScope_Old(y: int) {
      if y < 5 {
        label Treasure:
        assert true;
      }
      assert old(x) == old@Treasure(x);  // error: no label Treasure in scope
      assert 10 == old@WonderfulLabel(x);  // error: no label WonderfulLabel in scope
    }
    method LabelNotInScope_Unchanged(y: int) {
      if y < 5 {
        label Treasure:
        assert true;
      }
      assert unchanged@Treasure(`x);  // error: no label Treasure in scope
      assert unchanged@WonderfulLabel(this);  // error: no label WonderfulLabel in scope
    }
  }
}

// ----- bad use of types without zero initializers -----

module Initialization {
  datatype Yt<Y> = MakeYt(x: int, y: Y)
  type Even = x | x % 2 == 0
  type Odd = x | x % 2 == 1 witness 17
  type GW = x | x % 2 == 1 ghost witness 17
  method DefiniteAssignmentViolation() returns (e: Yt<Even>, o: Yt<Odd>, g: Yt<GW>)
  {
  }  // no resolution errors (but verification errors, see NonZeroInitialization.dfy)
  method ArrayElementInitViolation() returns (e: array<Yt<Even>>, o: array<Yt<Odd>>, g: array<Yt<GW>>)
  {
    e := new Yt<Even>[20];
    o := new Yt<Odd>[20];
    g := new Yt<GW>[20];
  }  // no resolution errors (but verification errors, see NonZeroInitialization.dfy)
  method GimmieOne<G(0)>() returns (g: G)
  {
  }
  method TypeParamViolation() returns (e: Yt<Even>, o: Yt<Odd>, g: Yt<GW>)
  {
    e := GimmieOne<Yt<Even>>();
    o := GimmieOne<Yt<Odd>>();  // error: cannot pass Yt<Odd> to a (0)-parameter
    g := GimmieOne<Yt<GW>>();  // error: cannot pass Yt<GW> to a (0)-parameter
  }
}

// ----------------- regression tests ----------------------------------------------------

module FreshTypeInferenceRegression {
  class MyClass {
    method M(N: nat)
    {
      var i, os := 0, {};
      while i < N
        invariant fresh(os)
        invariant forall o :: o in os ==> fresh(o.inner)  // error: type of "o" not yet known (this once caused a crash)
      {
        var o := new Outer();
        os, i := os + {o}, i + 1;
      }
    }
  }

  class Outer {
    const inner: Inner
    constructor ()
      ensures fresh(inner)
    {
      inner := new Inner();
    }
  }

  class Inner {
    constructor ()
  }
}

module RegressionTest {
  class Cache<X> {
    method Lookup(K: X) returns (V: X)
    {
      V := Cache[K];  // error: Cache is not a field but a type
    }
  }
}

module ExistsImpliesWarning {
  method M(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    requires exists i :: 0 <= i < a.Length ==> a[i] == b[i]  // warning
    requires exists i :: true && (0 <= i < a.Length ==> a[i] == b[i])
    requires exists i :: (0 <= i < a.Length ==> a[i] == b[i])
    requires exists i | 0 <= i < a.Length :: true ==> a[i] == b[i]
    requires exists i | 0 <= i < a.Length :: a[i] == b[i]
    requires exists i | 0 <= i < a.Length ==> a[i] == b[i] :: true
    requires exists i :: !(0 <= i < a.Length) || a[i] == b[i]
    requires exists i :: a[i] == b[i] <== 0 <= i < a.Length  // warning
    requires exists i :: !(0 <= i < a.Length && a[i] != b[i])
    requires exists i :: 0 <= i < a.Length && a[i] == b[i]
    requires exists i :: true ==> (0 <= i < a.Length && a[i] == b[i])  // warning
  {
  }

  method N(a: array<int>, b: array<int>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < a.Length ==> a[i] == b[i]
    requires forall i :: true && (0 <= i < a.Length ==> a[i] == b[i])
    requires forall i :: (0 <= i < a.Length ==> a[i] == b[i])
    requires forall i | 0 <= i < a.Length :: true ==> a[i] == b[i]
    requires forall i | 0 <= i < a.Length :: a[i] == b[i]
    requires forall i | 0 <= i < a.Length ==> a[i] == b[i] :: true
    requires forall i :: !(0 <= i < a.Length) || a[i] == b[i]
    requires forall i :: a[i] == b[i] <== 0 <= i < a.Length
    requires forall i :: !(0 <= i < a.Length && a[i] != b[i])
    requires forall i :: 0 <= i < a.Length && a[i] == b[i]
    requires forall i :: true ==> (0 <= i < a.Length && a[i] == b[i])
  {
  }
}

// --------------- ghost (regression) tests, receivers -------------------------------------

module GhostReceiverTests {
  class C {
    function F(x: int): int { 3 }
    function method G(x: int): int { 4 }
    lemma L(x: int) { }
    method M(x: int) { }
  }
  method Caller(x: int, ghost z: int, c: C, ghost g: C) {
    {
      var y;
      y := c.F(x);  // error: LHS is non-ghost, so RHS cannot use ghost function F
      y := g.F(x);  // error: LHS is non-ghost, so RHS cannot use ghost function F
      y := c.G(x);
      y := g.G(x);  // error: LHS is non-ghost, so RHS cannot use ghost variable g
    }
    {
      // all of the these are fine, because: the LHS is ghost and, therefore, the whole statement is
      ghost var y;
      y := c.F(x);
      y := g.F(x);
      y := c.G(x);
      y := g.G(x);
    }
    {
      // all of the these are fine, because: the LHS is ghost and, therefore, the whole statement is
      ghost var y;
      y := c.F(z);
      y := g.F(z);
      y := c.G(z);
      y := g.G(z);
    }
    c.L(x);
    g.L(x);
    c.M(x);
    g.M(x);  // error: cannot pass ghost receiver to compiled method
  }
}

// --------------- ghost RHS of constants (regression) tests -------------------------------------

module GhostRhsConst {
  class C {
    function F(n: nat): nat { n }  // a ghost function

    const b := F(0);  // error: RHS uses a ghost function
    static const u := F(0);  // error: RHS uses a ghost function
  }

  trait R {
    function F(n: nat): nat { n }  // a ghost function

    const b := F(0);  // error: RHS uses a ghost function
    static const u := F(0);  // error: RHS uses a ghost function
  }
}

// --------------- errors from nested modules -------------------------------------

module ErrorsFromNestedModules {
  method M() {
    U.V.Test();
    UU.V.Test();
  }

  module U {  // regression test: since U is rather empty, this had once caused an error
    module V {
      method Test() {
      }
      module W {
        const x1 := 12 * false  // error: bad types
      }
    }
  }

  module UU.V {  // same regression as above
    method Test() {
    }
    module W {
      const x1 := 12 * false  // error: bad types
    }
  }
}

// --------------- name clashes related to prefix-named modules -------------------------------------

module NameClashes {
  module U.G {
  }
  module U {
    class G { }  // error: duplicate name: G
    class H { }
  }
  module U.H {  // error: duplicate name: H
  }
}

// --------------- regression ghost tests -------------------------------------

module RegressionGhostTests {
  class Cell {
    var data: int
  }

  method field(x: Cell)
    modifies x
  {
    ghost var y := x;
    x.data := 42;
    y.data := 42;  // error: assignment to non-ghost field depends on a ghost
    (assert x == y; x).data := 42;
    (assert x == y; y).data := 42;  // error: assignment to non-ghost field depends on a ghost
  }

  method arr(a: array<int>)
    requires 5 < a.Length
    modifies a
  {
    ghost var b := a;
    ghost var i := 5;
    a[i] := 42;  // error: assignment to non-ghost field depends on a ghost
    b[5] := 42;  // error: assignment to non-ghost field depends on a ghost
  }

  method arr2(a: array2<int>)
    requires 5 < a.Length0 && 5 < a.Length1
    modifies a
  {
    ghost var b := a;
    ghost var i := 5;
    a[i,5] := 42;  // error: assignment to non-ghost field depends on a ghost
    a[5,i] := 42;  // error: assignment to non-ghost field depends on a ghost
    b[5,5] := 42;  // error: assignment to non-ghost field depends on a ghost
  }
}

// --------------- regression test const in frame expression ------------------------------

module RegressionConstFrameExpression {
  class C {
    const x: int
    var y: int
  }
  method m(c: C)
    modifies c`x
    modifies c`y
    ensures unchanged(c`x)
    ensures unchanged(c)
  {

  }
}

// --------------- change in language semantics to forbid !! on maps ------------------------------

module MapDisjointnessNoMore {
  method M<X,Y>(a: map, b: map) {
    assert a !! b;  // error: !! is (no longer) support on maps
    assert a.Keys !! b.Keys;  // instead, this is the way to do it
  }
}

// --------------- expect statements ------------------------------

module ExpectStatements {

  function UnsafeDivide(a: int, b: int): int {
    expect b != 0;  // expect statement is not allowed in this context
    a / b
  }

  method M() {
    ghost var g := 5;
    expect forall i : int :: i == i;  // error: quantifiers in non-ghost contexts must be compilable
    expect false, if g == 5 then "boom" else "splat"; // error: ghost variables are allowed only in specification contexts
  }
}

// --------------- type-parameter scopes ------------------------------

module TypeParameterScopes {
  class C<X> {
    function method G(): X
    method M<X>(f: X) {
      var h: X := f;
      var k: X := G();  // error: this is the wrong X
    }
    function method F<X>(f: X): int {
      var h: X := f;
      var k: X := G();  // error: this is the wrong X
      10
    }
  }
}

// --------------- type of function members (regression tests) ------------------------------

module TypeOfFunctionMember {
  function Fo<X>(x: X): int

  lemma M() {
    // Both of the following once crashed the type checker
    var rd := Fo<real>.reads;
    var rq := Fo<real>.requires;
  }
}

// --------------- update operations ------------------------------

module CollectionUpdates {
  // Update operations on collections must have the right types, modulo subset types.
  // For verification errors, see Maps.dfy.
  trait Trait { }
  class Elem extends Trait { }

  method UpdateValiditySeq(d: Trait, e: Elem) {
    var s: seq<Elem> := [e, e, e, e, e];
    s := s[1 := d];  // error: d is not an Elem (and is not a subset type of it, either)
  }
  method UpdateValidityMultiset(d: Trait) {
    var s: multiset<Elem>;
    s := s[d := 5];  // error: element value is not a Elem
  }
  method UpdateValidityMap(d: Trait, e: Elem) {
    var m: map<Elem, Elem>;
    if * {
      m := m[d := e];  // error: key is not a Elem
    } else {
      m := m[e := d];  // error: value is not a Elem
    }
  }
}
