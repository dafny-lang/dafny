// RUN: %exits-with 4 %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function power(b: int, n: nat): int
{
  if (n==0) then 1 else b*power(b, n-1)
}

method test_power()
  ensures power(power(2, 2), 2)==16
{
  // Enabling following assert makes the test pass
  //assert power(8, 5) == 32768;
} 