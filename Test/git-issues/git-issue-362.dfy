// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method IsLetter(c: char): bool { 'A' <= c <= 'Z' }
type Letter = c: char | IsLetter(c) witness 'A'
function Test(c: Letter): Letter {
  var r := c + 1 as char;
  assert true;   // <-- the error "value does not satisfy the subset constraints of 'Letter'" had been reported here
  r              // <-- this is the proper place to report the error
}
