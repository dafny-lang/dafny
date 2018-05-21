function abs(x: int): int
{
   if x < 0 then -x else x
}
method Abs(x: int) returns (y: int)
  // Use abs here, then confirm the method still verifies.
{
   // Then change this body to also use abs.
   if (x < 0)
     { return -x; }
   else
     { return x; }
}