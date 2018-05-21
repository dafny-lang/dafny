method m ()
{
   var i := 20;
   while (0 < i)
      invariant 0 <= i;
      decreases i;
   {
      i := i - 1;
   }
}