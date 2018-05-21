ghost method DistributiveLemma(a: seq<bool>, b: seq<bool>)
   ensures count(a + b) == count(a) + count(b);
{
   
}

function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   ((if a[0] then 1 else 0) + count(a[1..]))
}