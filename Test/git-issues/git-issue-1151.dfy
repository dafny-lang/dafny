// RUN: %baredafny run %args --relax-definite-assignment "%s" %S/git-issue-1151-concrete.cs > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "M"} M {
  type {:extern "T"} T
  method {:extern} GetT() returns (t: T)

  datatype D = D(t: T)
  datatype E<X> = E(t: T, x: X)

  type {:extern "U"} U(0)
  type {:extern "V"} V(0)
  datatype F = F(u: U, v: V)
}

method Main() {
  var t := M.GetT();

  var d: M.D;
  d := M.D(t);
  print d, "\n";

  var e: M.E<int>;
  e := M.E(t, 45);
  print e, "\n";

  var f: M.F;
  print f, "\n";
}
