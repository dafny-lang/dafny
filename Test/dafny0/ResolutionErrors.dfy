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
} //HereAreMoreGhostTests
module MiscMore { method DuplicateLabels(n: int) {
  var x;
  if (n < 7) {
    label DuplicateLabel: x := x + 1;
  } else {
    label DuplicateLabel: x := x + 1;
  }
  label DuplicateLabel: x := x + 1;
  label DuplicateLabel: {
    label AnotherLabel:
    label DuplicateLabel:  // error: duplicate label
    label OneMoreTime:
    x := x + 1;
  }
  label DuplicateLabel:
  label DuplicateLabel:  // error: duplicate label
  x := x + 1;
  label DuplicateLabel: x := x + 1;
}

// --------------- constructors -------------------------------------

class ClassWithConstructor {
  var y: int;
  method NotTheOne() { }
  constructor InitA() { }
  constructor InitB() modifies this; { y := 20; }
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
  y.data := z.data;  // this will have the effect of unifying all type args so far to be 'int'
  assert x.data == 5;  // this is type correct

  var w := new GenericClass<bool>;
  MG0(x, w);  // error: types don't match up
}

datatype GList<T> = GNil | GCons(hd: T, tl: GList)

method MG1(l: GList, n: nat)
{
  if (n != 0) {
    MG1(l, n-1);
    MG1(GCons(12, GCons(20, GNil)), n-1);
  }
  var t := GCons(100, GNil);
  t := GCons(120, l);  // error: types don't match up (List<T$0> versus List<int>)
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
    modifies this;
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
  datatype List<T> = Nil | Cons(T, List)
  datatype Tree<A,B> = Leaf(A, B) | Node(Tree, Tree<B,A>)

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
    ensures exists o: G :: o != null && fresh(o);
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
    var T4 :| T4 <= S;
  }
}

// ------------------------- lemmas ------------------------------
module MiscLemma { class L { }
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
    var j := var tb := F(); 5;  // error: allowed only if 'tb' were ghost
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
        var t2 := ghost var y := z; y + 3;  // error: 'y' can only be used in ghost contexts
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
} }
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
  lemma C() { var x := set o : object | true :: o; }

  method D() { var x := set o : object | true :: o; }  // error: not (easily) compilable
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
    var b2 := forall c: C :: c in {null} ==> c == null;  // error: type of s underspecified

    // In the following, the type of the bound variable is completely determined.
    var S: set<set<int>>;
    ghost var d0 := forall s :: s == {7} ==> s != {};
    var d1 := forall s: set :: s in S ==> s == {};
    var ggcc0: C;
    var ggcc1: C;  // error: full type cannot be determined
    ghost var d2 := forall c: C :: c != null ==> c.f == 10;
    ghost var d2' := forall c: C :: c == ggcc0 && c != null ==> c.f == 10;
    ghost var d2'' := forall c: C :: c == ggcc1 && c != null ==> c.f == c.f; // error: here, type of c is not determined

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
} } module FrameTargetFields_More {  class C {    var x: int    var y: int    ghost var z: int
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
    var g1 := d.g;  // error: cannot use ghost member in non-ghost code
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
    var x := var y :| y < z; y;  // error: contraint depend on ghost (z)
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
    requires c != null
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
    requires c != null
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
    requires c != null
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
    requires c != null
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
    requires c != null
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
    requires d != null && d.Length == 100 == |e|
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
