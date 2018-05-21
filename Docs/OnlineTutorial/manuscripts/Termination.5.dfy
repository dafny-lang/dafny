function Ack(m: nat, n: nat): nat
   decreases m, n;
{
   if m == 0 then n + 1
   else if n == 0 then Ack(m - 1, 1)
   else Ack(m - 1, Ack(m, n - 1))
}