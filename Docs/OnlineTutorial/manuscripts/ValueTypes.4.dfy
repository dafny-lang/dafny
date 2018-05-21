method m()
{
   assert 5 in {1,3,4,5};
   assert 1 in {1,3,4,5};
   assert 2 !in {1,3,4,5};
   assert forall x :: x !in {};
}