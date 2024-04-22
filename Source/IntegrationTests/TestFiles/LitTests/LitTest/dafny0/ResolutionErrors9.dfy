// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --allow-axioms


// --------------- regressions: using "this" in places where there is no enclosing class/type ------------------------------

module UseOfThis {
  // The following uses of "this." once caused the resolver to crash.

  type {:badUseOfThis this.K} OpaqueType { // error: cannot use "this" here
    const K: int
  }

  newtype {:badUseOfThis this.x} Newtype = // error: cannot use "this" here
    x: int | this.u // error: cannot use "this" here
    witness this.u // error: cannot use "this" here
  {
    const K: int
  }

  type {:badUseOfThis this.x} SynonymType = int // error: cannot use "this" here

  type {:badUseOfThis this.x} SubsetType = // error: cannot use "this" here
    x: int | this.u // error: cannot use "this" here
    witness this.u // error: cannot use "this" here

  trait {:badUseOfThis this.K} MyTrait { // error: cannot use "this" here
    const K: int
  }

  class {:badUseOfThis this.M} MyClass { // error: cannot use "this" here
    const M: int

    var {:goodUseOfThis this.M} I: int
    const {:goodUseOfThis this.M} J := 3
    method {:goodUseOfThis this.M} CM()
      ensures {:goodUseOfThis this.M} true
    ghost function {:goodUseOfThis this.M} CF(): int
      ensures {:goodUseOfThis this.M} true

    static const {:badUseOfThis this.M} L := 3 // error: cannot use "this" here
    static const N := this.M // error: cannot use "this" here
    static method {:badUseOfThis this.M} SM() // error: cannot use "this" here
      ensures {:badUseOfThis this.M} true // error: cannot use "this" here
    static ghost function {:badUseOfThis this.M} SF(): int // error: cannot use "this" here
      ensures {:badUseOfThis this.M} true // error: cannot use "this" here
  }

  datatype Datatype =
    | {:badUseOfThis this.K} DatatypeCtor // error: cannot use "this" here
  {
    const K: int
  }
}

module AutoInitTypeCheckRegression {
  codatatype AutoStream<G(0)> = AutoNext(head: G, tail: AutoStream<G>)

  function In<G>(a: AutoStream<G>): int // error: the argument to AutoStream is supposed to be an auto-init type
  function Out<G>(g: G): AutoStream<G> // error: the argument to AutoStream is supposed to be an auto-init type

  method M<G>(a: AutoStream<G>) // error: the argument to AutoStream is supposed to be an auto-init type
  method N<G>(g: G) returns (a: AutoStream<G>) // error: the argument to AutoStream is supposed to be an auto-init type
}

module ClassConstructorTests {
  class ClassWithConstructor {
    var y: int
    method NotTheOne() { }
    constructor InitA() { }
    constructor InitB() { y := 20; }
  }

  class ClassWithoutConstructor {
    method Init() modifies this { }
  }

  method ConstructorTests()
  {
    var o := new object;  // fine: does not have any constructors

    o := new ClassWithoutConstructor;  // fine: don't need to call any particular method
    o := new ClassWithoutConstructor.Init();  // this is also fine

    var c := new ClassWithConstructor.InitA();
    c := new ClassWithConstructor;  // error: must call a constructor
    c := new ClassWithConstructor.NotTheOne();  // error: must call a constructor, not an arbitrary method
    c := new ClassWithConstructor.InitB();
  }

  class Y {
    var data: int
    constructor (x: int)
    {
      data := x;
    }
    method Test() {
      var i := new Y(5);
      i := new Y(7);
      i := new Y;  // error: the class has a constructor, so one must be used
      var s := new Luci.Init(5);
      s := new Luci.FromArray(null);
      s := new Luci(false);
      s := new Luci(true);
      s := new Luci.M();  // error: there is a constructor, so one must be called
      s := new Luci;  // error: there is a constructor, so one must be called
      var l := new Lamb; // fine, since there are no constructors (only methods)
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
}

module DefaultValues {
  method Test() {
    var r := 3 + MyFunction(7);
  }

  function MyFunction(n: int, acc: int := n * false): int { // note, badly type default-value expression
    20
  }
}

module IndexAdviceTypeRegressions {
  type BV10 = x: bv10 | x != 999 witness 8

  method Index(s: seq<string>)
    requires 2 < |s|
  {
    var k: bv10 := 2;
    var a := s[k := "tjena"];

    var K: BV10 := 2;
    var A := s[K := "tjena"];

    // rely on advice for the type
    var i;
    var b := s[i := "tjena"];
  }

  method Multi(matrix: array2<real>)
    requires matrix.Length0 == matrix.Length1 == 100
  {
    var u := matrix[2, 5];
    var i := 2;
    u := matrix[i, 5];
    var j := 2;
    u := matrix[j, 5];
    j := j & j;
    j := 16 as bv29;
    // rely on advice for the type
    var k;
    u := matrix[k, 5];
  }

  method Array(arr: array<real>) returns (r: real)
    requires 10 <= arr.Length
  {
    var k: bv10 := 2;
    r := arr[k];
    var K: BV10 := 2;
    r := arr[K];
  }

  method Seq(s: seq<real>) returns (r: real)
    requires 10 <= |s|
  {
    var k: bv10 := 2;
    r := s[k];
    var K: BV10 := 2;
    r := s[K];
  }

  method Range(arr: array<real>, s: seq<real>) returns (r: seq<real>)
    requires 10 <= arr.Length <= |s|
  {
    var k: bv10 := 2;
    var K: BV10 := 4;
    r := arr[k..K];
    r := s[k..K];
    r := arr[k..];
    r := s[k..];
    r := arr[..K];
    r := s[..K];

    // rely on advice for the type
    var a, b, c, d;
    r := arr[a..b];
    r := arr[c..];
    r := arr[..d];
    var w, x, y, z;
    r := s[w..x];
    r := s[y..];
    r := s[..z];
  }

  method Bad(arr: array<real>, s: seq<real>, matrix: array2<real>) returns (r: real, range: seq<real>) {
    r := arr[2.3]; // error: bad index type
    r := s[2.3]; // error: bad index type
    r := matrix[false, 2.3]; // error: bad index type

    range := arr[2.3..3.14]; // error (x2): bad index types
    range := arr[2.3..]; // error: bad index type
    range := arr[..3.14]; // error: bad index type
    range := s[2.3..3.14]; // error (x2): bad index types
    range := s[2.3..]; // error: bad index type
    range := s[..3.14]; // error: bad index type
  }
}
