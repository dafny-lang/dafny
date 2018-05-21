method Abs(x: int) returns (y: int)
   ensures 0 <= y;
   ensures 0 <= x ==> x == y;
   ensures x < 0 ==> y == -x;
{
   if (x < 0)
     { return -x; }
   else
     { return x; }
}