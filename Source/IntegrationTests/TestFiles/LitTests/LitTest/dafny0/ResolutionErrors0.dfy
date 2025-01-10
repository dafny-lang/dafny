// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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
    requires b != null
  {
    while
    {
      case b[x,y] == s =>
    }
  }

  // -------- name resolution

  class Global {
    var X: int
    function F(x: int): int { x }
    static ghost function G(x: int): int { x }
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

  ghost function Tuv(arg0: Abc, arg1: bool): int { 10 }

  class EE {
    var Eleanor: bool
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

      }
      var dd;
      dd := GhostDt.Nil(g);  // fine
      dd := GhostDt.Cons(g, dt, 2);  // error: cannot pass 'g' as non-ghost parameter
      ghost var dtg := GhostDt.Cons(g, dt, 2);  // fine, since result is ghost
    }
    ghost function F(x: int, y: int): int {
      y
    }
    function G(x: int, ghost y: int): int {
      y  // error: cannot return a ghost from a non-ghost function
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
        invariant n <= 112
        decreases 112 - n
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
        invariant n <= 112
        decreases 112 - n
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
        invariant n <= 112
        decreases 112 - n
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
  // Note, more tests in module ClassConstructorTests below

  class ClassWithConstructor {
    var y: int
    method NotTheOne() { }
    constructor InitA() { }
    constructor InitB() modifies this { y := 20; }  // error: don't use "this" in modifies of constructor
  }

  method ConstructorTests()
  {
    var c := new ClassWithConstructor.InitB();
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
  class GenericClass<T> { var data: T }

  method MG0(a: GenericClass, b: GenericClass)
    requires a != null && b != null
    modifies a
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
    ghost var ycalc: int

    ghost method Mod(a: int)
      modifies this
      ensures ycalc == a
    {
      ycalc := a;
    }

    ghost method Bad()
      modifies this
      ensures 0 == 1
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
    var data: int
    constructor (x: int)
    {
      data := x;
    }
    constructor (y: bool)  // error: duplicate constructor name
    {
    }
    method Test() {
      var i := new Y(5);
      i := new Y(7);

      var s := new Luci.Init(5);
      s := new Luci.FromArray(null);
      s := new Luci(false);
      s := new Luci(true);

      var l := new Lamb;
      l := new Lamb();  // error: there is no default constructor
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

// ----- One more phase of HereAreMoreGhostTests from above

module HereAreMoreGhostTests' {
  datatype GhostDt =
    Nil(ghost extraInfo: int) |
    Cons(data: int, tail: GhostDt, ghost moreInfo: int)

  method M(dt: GhostDt) returns (r: int) {
    ghost var g := 5;
    match (dt) {
      case Nil(gg) =>
      case Cons(dd, tt, gg) =>
        r := G(dd, dd);  // fine
        r := G(dd, gg);  // fine
        r := G(gg, gg);  // error: cannot pass ghost 'gg' as non-ghost parameter to 'G'
    }
  }

  function G(x: int, ghost y: int): int

  function H(dt: GhostDt): int {
    match dt
    case Nil(gg) =>  gg  // error: cannot return a ghost from a non-ghost function
    case Cons(dd, tt, gg) =>  dd + gg  // error: ditto
  }
} // HereAreMoreGhostTests'
