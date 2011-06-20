
//Should not verify, as ghost loops should not be allowed to diverge.
method GhostDivergentLoop()
{
   var a := new int [2];
   a[0] := 1;
   a[1] := -1;
   ghost var i := 0;
   while (i < 2)
      decreases *; // error: not allowed on a ghost loop
      invariant i <= 2;
      invariant (forall j :: 0 <= j && j < i ==> a[j] > 0);
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

datatype Abc = Abel | Benny | Cecilia(y: int) | David(x: int) | Eleanor;
datatype Xyz = Alberta | Benny | Constantine(y: int) | David(x: int);
datatype Rst = David(x: int, y: int);

function Tuv(arg0: Abc, arg1: bool): int { 10 }
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
  var e := Eleanor;
  assert Tuv(e, this.Eleanor) == 10;
}

// --------------- ghost tests -------------------------------------

datatype GhostDt =
  Nil(ghost extraInfo: int) |
  Cons(data: int, tail: GhostDt, ghost moreInfo: int);

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
  ghost method NiceTry()
    ensures false;
  {
    while (true)
      decreases *;  // error:  not allowed in ghost context
    {
    }
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
            break break break;  // error: tries to break out of more loop levels than there are
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

method DuplicateLabels(n: int) {
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

datatype DTD_List = DTD_Nil | DTD_Cons(Car: int, Cdr: DTD_List);

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
      assert d == DTD_Cons(hd, tl);
  }
}
