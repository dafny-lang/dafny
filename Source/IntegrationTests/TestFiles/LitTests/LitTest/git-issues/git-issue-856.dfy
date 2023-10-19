// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var big := 9223372036854775808;
  var a := new int[big];
  assert a.Length == big;
  print a.Length == big;
}

