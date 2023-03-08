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

// Ostensibly, the following function is tail recursive. But the ghost-ITE optimization
// removes the tail call. This test ensures that the unused setup for the tail optimization
// does not cause problems.
function H(x: int, ghost y: nat): int {
  if y == 0 then
    x
  else
    H(x, y - 1)
}

// Like function H, function J looks like it's tail recursive. The compiler probably will
// emit the tail-call label, even though the tail-call is never taken.
function J(x: int): int {
  if true then
    x
  else
    J(x)
}

// The following function would never verify, and its execution wouldn't terminate.
// Nevertheless, we'll test here that it compiles into legal target code.
function {:verify false} K(x: int, ghost y: nat): int {
  K(x, y - 1)
}

method Main() {
  print F(5, 3), "\n"; // 65
  print G(5, 3), "\n"; // 65
  print H(65, 3), "\n"; // 65
  print J(65), "\n"; // 65
}
