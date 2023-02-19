// RUN: %dafny /compile:0 /functionSyntax:4 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /functionSyntax:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Implementation note: F's body is compiled using TrExprOpt
function F(x: nat, ghost y: nat): nat
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1) // this branch is not compiled (which even makes F tail recursive, using auto accumulator)
  else
    F(x - 1, 65) + 13
}

lemma AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
{
}

method Main() {
  print F(5, 3), "\n"; // 65
}
