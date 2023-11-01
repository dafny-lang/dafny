// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %exits-with 4 %baredafny verify %args --verify-included-files "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "Includee.dfy"

method test_include(z:int)
{
  // Make sure we can still see function bodies
  assert forall y :: f(y) == 2*y;

  // Use an unverified method
  var w := m_unproven(z);
  assert w == 2*z;
}

// and some refinement stuff, to make sure it works with includes
module Concrete refines Abstract
{
  function inc...  // error: postcondition violation
  {
    x - 1
  }
  method M...
  {
    var y := G(x);  // error: it is not know whether or not G(x) is non-negative, as required
    if x < 68 {
      return 70;  // error
    } else if 30 <= x {  // this will always be true here
      return x;  // fine
    }
    ...;
  }
}
