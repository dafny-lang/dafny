ghost method DistributiveLemma(a: seq<bool>, b: seq<bool>)
   requires a == [];
   ensures count(a + b) == count(a) + count(b);
{
   if (a == [])
   {
      assert a + b == b;
   }
   else
   {
      DistributiveLemma(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
   }
}

function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   ((if a[0] then 1 else 0) + count(a[1..]))
}