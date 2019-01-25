// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt = Nil | Cons(head: int, tail: Dt)

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
}

function method Up(m: nat, n: nat): Dt
  requires m <= n
  decreases n - m
{
  if m == n then Nil else Cons(m, Up(m+1, n))
}

function method Sum(xs: Dt): int {
  match xs  // top-level match expression
  case Nil => 0
  case Cons(x, tail) => x + Sum(tail)
}

function method SumAgain(xs: Dt): int {
  var r := match xs  // let expression; non-top-level match expression
    case Nil => 0
    case Cons(x, tail) => x + SumAgain(tail);
  r
}

method PrintSum(xs: Dt, prefix: string) {
  match xs  // match statement
  case Nil =>
  case Cons(x, tail) =>
    print prefix, x;
    PrintSum(tail, " + ");  // tail recursion
}
