method hail(n: nat)
{
   while(1 < n)
      decreases *;
   { 
      n := if n % 2 == 0 then n / 2 else n * 3 + 1;
   }
}