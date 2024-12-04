// RUN: %exits-with -any %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Attributes on top-level declarations

@AutoContracts   // Can't apply that on functions
@NativeIntOrReal // Can't apply that on functions
@NativeInt       // Can't apply that on functions
@NativeNone      // Can't apply that on functions
@NativeUInt8     // Can't apply that on functions
@NativeInt8      // Can't apply that on functions
@NativeUInt16    // Can't apply that on functions
@NativeInt16     // Can't apply that on functions
@NativeUInt32    // Can't apply that on functions
@NativeInt32     // Can't apply that on functions
@NativeInt53     // Can't apply that on functions
@NativeUInt64    // Can't apply that on functions
@NativeInt64     // Can't apply that on functions
@NativeUInt128   // Can't apply that on functions
@NativeInt128    // Can't apply that on functions
@DisableNonlinearArithmetic // Can't apply that on functions
function f(x:int) : bool
  requires x > 3
{
  x > 7
}

@AutoRequires                        // Makes no sense on modules
@AutoRevealDependenciesAll(false)    // Makes no sense on modules
@AutoRevealDependenciesAll(true)     // Makes no sense on modules
@AutoRevealDependencies(level := 10) // Makes no sense on modules
@Axiom                               // Makes no sense on modules
@Concurrent                          // Makes no sense on modules
@TailRecursion                       // Makes no sense on modules
@VerifyOnly                          // Not supported on modules                      
@Print                               // Not supported on modules
@Priority(2)                         // Not supported on modules
@ResourceLimit(1000)                 // Not supported on modules
@TimeLimit(1000)                     // Not supported on modules
@TimeLimitMultiplier(2)              // Not supported on modules
@Verify                              // Not supported on modules
@Test                                // Not supported on modules
@TestInline                          // Not supported on modules
@TestInline(10)                      // Not supported on modules
@TestEntry                           // Not supported on modules
@VcsMaxCost(10)                      // Not supported on modules
@VcsMaxKeepGoingSplits(10)           // Not supported on modules
@VcsMaxSplits(10)                    // Not supported on modules
@IsolateAssertions                   // Not supported on modules
@Synthesize                          // Not supported on modules
module Dummy {
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

@Fuel(1, 2) // Fuel not supported on type synonyms
type NewInt = int

@Fuel(1, 2) // Fuel not supported on subset types
type NewInt2 = x: int | x >= 0 witness *

@Fuel(1, 2) // Fuel not supported on subset types
newtype NewInt3 = int

@isolate_assertions // Should be IsolateAssertions 
@IsolateAssertions("noargument") // Should have no argument.
// Above is not treated as a @call with label "IsolateAssertion"
@Transparent // Makes no sense on method
method Test(a: int, b: int, c: int)
  requires a < b && b < c
{
  assert a < c; 
  assert c > a;
}
