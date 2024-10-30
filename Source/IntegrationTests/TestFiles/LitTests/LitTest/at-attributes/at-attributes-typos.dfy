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
@Compile(true && false)
@fuel(low := 1, 2) // Should be Fuel
@Fuel(2, low := 1) // Wrong position of arguments
function g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}

@Fuel(1, 2)  // Fuel not supported on datatype
datatype Useless = Useless

@Fuel(1, 2)  // Fuel not supported on codatatype
codatatype UselessCodatatype = UselessCodatatype

@Fuel(1, 2) // Fuel not supported on method
method g_method() {
}

@Fuel(1, 2) // Fuel not supported on type synonyms
type NewInt = int

@Fuel(1, 2) // Fuel not supported on subset types
type NewInt2 = x: int | x >= 0 witness *

@Fuel(1, 2) // Fuel not supported on subset types
newtype NewInt3 = int

@isolate_assertions // Should be IsolateAssertions 
@IsolateAssertions("noargument") // Should have no argument.
// Above is not treated as a @call with label "IsolateAssertion"
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  assert a < c; 
  assert c > a;
}
