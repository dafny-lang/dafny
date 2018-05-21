method m(n: nat)
{
   var i: int := 0;
   while (i < n)
      invariant 0 <= i;
   {
      i := i + 1;
   }
   assert i == n;
}