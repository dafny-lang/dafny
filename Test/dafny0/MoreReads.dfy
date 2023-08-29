// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// reads checks for default-value expressions

ghost function F0(x: int := var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; 100): int {
  2
}

ghost function F1(x: int := var bb := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100; 100): int { // error: precondition on .reads
  2
}

ghost function F2(obj: object,
  x: int := var bb := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; 100 // error: insufficient reads on .reads
  ) : int
{
  2
}

ghost function F3(obj: object,
  x: int := var bb := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; 100
  ) : int
  reads obj
{
  2
}

datatype Dt =
  | Ctor0(ghost x: int := var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; 100)
  | Ctor1(ghost x: int := var bb := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100; 100) // error: precondition on .reads
  | Ctor2(obj: object,
          ghost x: int := var bb := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; 100) // error: insufficient reads on .reads

method M0(ghost x: int := var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; 100) {
}

method M1(ghost x: int := var bb := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100; 100) {
}

iterator Iter(ghost x: int := var bb := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100; 100) {
}

// delayed reads checks in reads clauses and functon bodies

ghost function P(): int
  requires exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100
{
  var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; // error: precondition on .reads
  var cc := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100;
  var f: int ~> int :| f.requires(10) && f.reads(10) == {} && f(10) == 100;
  var g: int ~> int :| g.reads(10) == {} && g.requires(10) && g(10) == 100; // error: precondition on .reads
  f(10) + g(10)
}

ghost function R0(): int
  requires exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100
  reads
    var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; // error: precondition on .reads
    var cc := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100;
    {}
{
  100
}

ghost function R1(obj: object): int
  reads
    var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
    var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
    {}
{
  100
}

ghost function R2(obj: object): int
  reads
    var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
    var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
    {obj}
{
  100
}

ghost function R3(obj: object): int
  reads
    var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
    var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
    {}
  reads obj
{
  100
}

// lambda expressions

method Lambda0() {
  var f :=
    (x: int)
    requires x < 100
    reads if x == 202 then var u := 10/0; {} else {} // no problem, because of precondition
    =>
    2;
  var g :=
    (x: int)
    reads if x == 202 then var u := 10/0; {} else {} // no problem, because of precondition
    requires x < 100
    =>
    2;
}

method Lambda1() {
  var p :=
    ()
    requires exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100
    =>
    var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; // error: precondition on .reads
    var cc := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100;
    var f: int ~> int :| f.requires(10) && f.reads(10) == {} && f(10) == 100;
    var g: int ~> int :| g.reads(10) == {} && g.requires(10) && g(10) == 100; // error: precondition on .reads
    f(10) + g(10);

  var r0 :=
    ()
    requires exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100
    reads
      var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {} && f(10) == 100; // error: precondition on .reads
      var cc := exists f: int ~> int :: f.reads(10) == {} && f.requires(10) && f(10) == 100;
      {}
    =>
    100;

  var r1 :=
    ()
    reads
      var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
      var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
      {}
    =>
    100;

  var r2 :=
    ()
    reads
      var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
      var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
      {obj}
    =>
    100;

  var r3 :=
    ()
    reads
      var bb := exists f: int ~> int :: f.requires(10) && f.reads(10) == {obj} && f(10) == 100; // error: precondition on .reads
      var cc := exists f: int ~> int :: f.reads(10) == {obj} && f.requires(10) && f(10) == 100; // error: insufficient reads clause on .reads
      {}
    reads obj
    =>
    100;
}

// lambda expressions are not subject to enclosing reads clause

class Cell {
  var data: int
}

function LambdaInsideLambda0(cell: Cell): int
{
  var f := () reads cell => cell.data; // fine
  2
}

function LambdaInsideLambda1(cell: Cell): int
{
  var f := () reads cell => cell.data;
  f() // error: LambdaInsideLambda1 has insufficient reads clause for this call
}

function LambdaInsideLambda2(cell: Cell): int
  reads cell
{
  var f := () reads cell => cell.data;
  f() // fine, since LambdaInsideLambda2 is allowed to read c
}
