method Abs(x: int) returns (y: int)
   // Add a precondition here.
   ensures 0 <= y;
   ensures 0 <= x ==> x == y;
   ensures x < 0 ==> y == -x;
{
   // Simplify the body to just one return statement
   if (x < 0)
     { return -x; }
   else
     { return x; }
}