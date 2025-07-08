// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment
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

function Up(m: nat, n: nat): List
  requires m <= n
  decreases n - m
{
  if m == n then Nil else Cons(m, Up(m+1, n))
}

function Sum(xs: List): int {
  match xs  // top-level match expression
  case Nil => 0
  case Cons(x, tail) => x + Sum(tail)
}

function SumAgain(xs: List): int {
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
predicate IsRed(b: Berry) {
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

module ModuleM {
  datatype OptionInt = Some(int) | None
}

method TestModule() {
  PrintMaybe(ModuleM.Some(1701));
}

method PrintMaybe(x: ModuleM.OptionInt) {
  match x
  case Some(n) => print n, "\n";
  case None => print "None\n";
}
