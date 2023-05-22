// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

type pos = i:int | i > 0 witness 1

datatype Generic<T> = Gen(p: T)

method Main() {
  var p: (pos, pos);
  var (a, b) := p;
  assert a > 0;
  assert b > 0;

  var e: Generic<pos>;
  var Gen(n) := e;
  assert n > 0;

  print "p=", p, " n=", n, "\n";
}
