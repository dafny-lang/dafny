// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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
