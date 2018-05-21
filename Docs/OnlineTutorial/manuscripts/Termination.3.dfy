function fac(n: nat): nat
{
   if n == 0 then 1 else n * fac(n-1)
}