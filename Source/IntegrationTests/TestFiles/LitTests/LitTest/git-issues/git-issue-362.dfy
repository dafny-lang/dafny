// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


function IsLetter(c: char): bool { 'A' <= c <= 'Z' }
type Letter = c: char | IsLetter(c) witness 'A'
ghost function Test(c: Letter): Letter {
  var r := c + 1 as char;
  assert true;   // <-- the error "value does not satisfy the subset constraints of 'Letter'" had been reported here
  r              // <-- this is the proper place to report the error
}
