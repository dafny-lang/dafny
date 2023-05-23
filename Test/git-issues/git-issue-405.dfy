// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const WITNESS := seq(10, i => 0)     // This line alone suffices to cause the original bug
type Seq10 = s: seq<int> | |s| == 10 witness WITNESS

function WITNESS2(): seq<int> { seq(10, i => 0) }
type Seq10a = s: seq<int> | |s| == 10 witness WITNESS2()

ghost const WITNESS3 := seq(10, i => 0)

class C {
  var x: int
  method M() returns (f: () ~> int)
    modifies this
    ensures f.requires()
  {
    x := 5;
    f := () => if 5 / x == 1 then 2 else 3;
    x := 0;
  }
}

method Main() {
  var c := new C;
  var f := c.M();
  print f(), "\n";
}
