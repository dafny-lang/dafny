method m(n: nat)
{
   var i: int := 0;
   while (i < n)
      invariant 0 <= i <= n;
   {
      i := i + 1;
   }
}