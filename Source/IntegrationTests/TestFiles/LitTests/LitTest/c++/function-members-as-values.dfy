// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// Instance, static and generic functions used as values.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class C {
  var k: i32
  constructor(k: i32) ensures this.k == k { this.k := k; }
  function Get(x: i32): i32 reads this { if -100 < x < 100 && -100 < k < 100 then x + k else 0 }
  function Pick<T>(x: T, y: T, first: bool): T { if first then x else y }
  static function Twice(x: i32): i32 { if -100 < x < 100 then x * 2 else x }
  // A function of `this` as a value, used after the method returns.
  method Self() returns (f: i32 ~> i32) ensures f.requires(1) { f := Get; }
}

class Box<T> {
  var v: T
  constructor(v: T) ensures this.v == v { this.v := v; }
  function Get(): T reads this { v }
  static function Same(x: T): T { x }
  method Read() returns (r: T) { var f := Get; r := f(); }
}

function Id<T>(x: T): T { x }

// The function value outlives the only other reference to its object.
method MakeGetter() returns (f: i32 ~> i32)
  ensures f.requires(1)
{
  var c := new C(10);
  f := c.Get;
}

method MakeSelf() returns (f: i32 ~> i32)
  ensures f.requires(1)
{
  var c := new C(20);
  f := c.Self();
}

method Main() {
  var c := new C(3);
  var get := c.Get;
  var twice := C.Twice;
  var idInt := Id<i32>;
  var idBool := Id<bool>;
  var pick := c.Pick<bool>;
  var getter := MakeGetter();
  var self := MakeSelf();
  var other := new C(50);
  print get(1), " ", twice(2), " ", idInt(5), " ", idBool(true), " ", pick(true, false, false), " ", getter(1), " ", self(1), "\n";

  var box := new Box<i32>(7);
  var read := box.Read();
  var same := Box<i32>.Same;
  print read, " ", same(8), "\n";
}
