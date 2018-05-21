method m2(a: seq<bool>, b:seq<bool>)
   requires |a| > 0;
{
   assert count(a) == count([a[0]]) + count(a[1..]);
}

function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   ((if a[0] then 1 else 0) + count(a[1..]))
}