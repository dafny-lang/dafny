method Abs(x: int) returns (y: int)
   // Add a pre-condition here so that the method verifies.
   // Don't change the postconditions.
   ensures 0 <= y;
   ensures 0 <= x ==> x == y;
   ensures x < 0 ==> y == -x;
{
  y:= x + 2;
}

method Abs2(x: int) returns (y: int)
   // Add a pre-condition here so that the method verifies.
   // Don't change the postconditions.
   ensures 0 <= y;
   ensures 0 <= x ==> x == y;
   ensures x < 0 ==> y == -x;
{
  y:= x + 1;
}