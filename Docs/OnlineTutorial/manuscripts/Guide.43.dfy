method m()
{
   var i, n := 0, 20;
   while (i != n)
      decreases n - i;
   {
      i := i + 1;
   }
}