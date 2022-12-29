// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
//
// This fragment of comp/Dt.dfy serves to facilitate incremental compiler development.

datatype List = Nil | Cons(head: int, tail: List)

method Main() {
  var a := Nil;
  var b := Cons(5, a);
  var c := (a, b);
  var d := (c.1, c.0);
  var e := ();
  print a, "\n";
  print b, "\n";
  print c, "\n";
  print d, "\n";
  print e, "\n";

  print b.head, " ", b.tail, "\n";

  var u := Up(0, 7);
  print u, "\n";
  var s := Sum(u);
  PrintSum(u, "");
  print " == ", s;
  s := SumAgain(u);
  print " (once more, that's ", s, ")\n";

  AllBerry();
  TestConflictingNames();
  TestModule();
}

function method Up(m: nat, n: nat): List
  requires m <= n
  decreases n - m
{
  if m == n then Nil else Cons(m, Up(m+1, n))
}

function method Sum(xs: List): int {
  match xs  // top-level match expression
  case Nil => 0
  case Cons(x, tail) => x + Sum(tail)
}

function method SumAgain(xs: List): int {
  var r := match xs  // let expression; non-top-level match expression
    case Nil => 0
    case Cons(x, tail) => x + SumAgain(tail);
  r
}

method PrintSum(xs: List, prefix: string) {
  match xs  // match statement
  case Nil =>
  case Cons(x, tail) =>
    print prefix, x;
    PrintSum(tail, " + ");  // tail recursion
}

datatype Berry = Smultron | Jordgubb | Hjortron | Hallon
predicate method IsRed(b: Berry) {
  b != Berry.Hjortron
}

method AllBerry() {
  var s := set b: Berry | IsRed(b);
  print s, "\n";
}

datatype ConflictingNames = ConflictingNames1(len: int, public: char, goto: string) | ConflictingNames2(goto: string)

method TestConflictingNames() {
  var x := ConflictingNames1(42, 'q', "hello");
  print x.len, " ", x.public, " ", x.goto, "\n";
}

module Module {
  datatype OptionInt = Some(int) | None
}

method TestModule() {
  PrintMaybe(Module.Some(1701));
}

method PrintMaybe(x : Module.OptionInt) {
  match x
  case Some(n) => print n, "\n";
  case None => print "None\n";
}
