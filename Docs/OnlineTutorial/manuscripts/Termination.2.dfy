method m()
{
   var i, n := 0, 11;
   while(i < n)
      decreases n - i;
   {
      // do something interesting
      i := i + 5;
   }
}