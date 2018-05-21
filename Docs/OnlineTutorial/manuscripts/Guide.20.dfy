method Abs(x: int) returns (y: int)
   ensures 0 <= y && (y == x || y == -x);
{
   if (x < 0)
     { return -x; }
   else
     { return x; }
}