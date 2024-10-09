// RUN: %exits-with -any %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Attributes on top-level declarations

function f(x:int) : bool
  requires x > 3
{
  x > 7
}

@compile("true") // Should be Compile
@Compile("true") // Should be boolean
@Compile(true, false) // Should have one argument
@fuel(low := 1, 2) // Should be Fuel
@Fuel(2, low := 1) // Wrong position of arguments
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}

@isolate_assertions // Should be IsolateAssertions 
@IsolateAssertions("noargument") // Should have no argument.
// Above is not treated as a @call with label "IsolateAssertion"
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  assert a < c; 
  assert c > a;
}
