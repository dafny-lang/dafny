method m(n: nat)
{
   var i := 0;
   while (i < n)
      invariant 0 <= i;
   {
      i := i + 1;
   }
}