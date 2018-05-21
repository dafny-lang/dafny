ghost method DistributiveLemma(a: seq<bool>, b: seq<bool>)
   requires a == [];
   ensures count(a + b) == count(a) + count(b);
{
   if (a == [])
   {
      assert a + b == b;
      assert count(a) == 0;
      assert count(a + b) == count(b);
      assert count(a + b) == count(a) + count(b);
   }
   else
   {
      //...
   }
}

function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   ((if a[0] then 1 else 0) + count(a[1..]))
}