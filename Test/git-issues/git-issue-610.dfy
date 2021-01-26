// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

type pos = i:int | i > 0 witness 1

method Main()
{
  var x:pos;
  assert x > 0;
  var p:(pos, pos);
  var (a, b) := p;
  assert a > 0;
  assert b > 0;
  print a, " ", b, "\n";
  expect a > 0;
  expect b > 0;
}

