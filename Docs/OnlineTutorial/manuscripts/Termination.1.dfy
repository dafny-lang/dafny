method m(n: nat)
{
   var i := 0;
   while(i < n)
      invariant 0 <= i <= n;
   {
      // do something interesting
      i := i + 1;
   }
}