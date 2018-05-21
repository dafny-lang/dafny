method m()
{
   assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};
}