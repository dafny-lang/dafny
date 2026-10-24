// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// Lambdas over `this`.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Counter {
  var k: i32
  const plus: i32 ~> i32 := x reads this => if -100 < x < 100 && -100 < k < 100 then x + k else 0
  const minus: i32 ~> i32 := Minus()
  constructor(k: i32) ensures this.k == k { this.k := k; }
  function Adder(): i32 ~> i32 reads this {
    x reads this => if -100 < x < 100 && -100 < k < 100 then x + k else 0
  }
  function Minus(): i32 ~> i32 {
    x reads this => if -100 < x < 100 && -100 < k < 100 then x - k else 0
  }
  function Self(): () -> Counter { () => this }
}

class Cell<T> {
  var v: T
  constructor(v: T) ensures this.v == v { this.v := v; }
  function Get(): () ~> T reads this { () reads this => v }
}

method MakeAdder() returns (f: i32 ~> i32)
  ensures f.requires(4)
{
  var c := new Counter(3);
  f := c.Adder();
}

method MakePlus() returns (f: i32 ~> i32)
  ensures f.requires(4)
{
  var c := new Counter(3);
  f := c.plus;
}

method Main() {
  // A lambda over `this` outlives every other reference to its object.
  var add := MakeAdder();
  var other := new Counter(50);
  print add(4), "\n";

  // So does an instance const holding one.
  var plus := MakePlus();
  var another := new Counter(60);
  print plus(4), "\n";

  // An instance const that a function builds.
  print other.minus(4), "\n";

  // A lambda that returns `this`.
  print other.Self()() == other, "\n";

  // A lambda over `this` in a generic class.
  var cell := new Cell<i32>(9);
  var get := cell.Get();
  print get(), "\n";
}
