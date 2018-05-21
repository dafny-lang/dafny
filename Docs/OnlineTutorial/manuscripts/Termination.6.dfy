function even(n: nat): bool 
   ensures even(n) <==> n % 2 == 0;
{
   if n == 0 then true else odd(n-1)
}
function odd(n: nat): bool 
   ensures odd(n) <==> n % 2 != 0;
{
   if n == 0 then false else even(n-1)
}