method m(n: nat)
{
   var i: int := 0;
   while (i < n) // Change this. What happens?
      invariant 0 <= i <= n;
   {
      i := i + 1;
   }
   assert i == n;
}