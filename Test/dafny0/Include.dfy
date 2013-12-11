
include "Includee.dfy"

method test_include(z:int)
{
  // Make sure we can still see function bodies
  assert forall y :: f(y) == 2*y;

  // Use an unverified method
  var w := m_unproven(z);
  assert w == 2*z;
}
