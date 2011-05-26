
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
