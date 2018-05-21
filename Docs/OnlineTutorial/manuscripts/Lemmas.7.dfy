function count(a: seq<bool>): nat
{
   if |a| == 0 then 0 else
   ((if a[0] then 1 else 0) + count(a[1..]))
}

method m()
{
   assert count([]) == 0;
   assert count([true]) == 1;
   assert count([false]) == 0;
   assert count([true, true]) == 2;
}