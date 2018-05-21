method m()
{
   assert {1} <= {1, 2} && {1, 2} <= {1, 2}; // subset
   assert {} < {1, 2} && !({1} < {1}); // strict, or proper, subset
   assert !({1, 2} <= {1, 4}) && !({1, 4} <= {1, 4}); // no relation
   assert {1, 2} == {1, 2} && {1, 3} != {1, 2}; // equality and non-equality
}