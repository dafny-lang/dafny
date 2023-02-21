// RUN: %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1) // this branch is not compiled (which even makes F auto-accumulator tail recursive)
  else
    F(x - 1, 60) + 13
}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

function G(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    var z := x + x;
    var a, b, c := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
    assert a + b + c == G(x, y - 1) + 300;
    b // this branch is not compiled (which even makes G auto-accumulator tail recursive)
  else
    G(x - 1, 60) + 13
}

method Main() {
  print F(5, 3), "\n"; // 65
  print G(5, 3), "\n"; // 65
}
