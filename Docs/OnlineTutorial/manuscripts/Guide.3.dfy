method Abs(x: int) returns (y: int)
   ensures 0 <= y;
{
   if (x < 0)
      { return -x; }
   else
      { return x; }
}