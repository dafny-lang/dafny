method m ()
{
   var s1 := {};
   var s2 := {1, 2, 3};
   var s3, s4 := {1,2}, {1,4};
   assert s2 + s4 == {1,2,3,4}; // set union
   assert s2 * s3 == {1,2} && s2 * s4 == {1}; // set intersection
   assert s2 - s3 == {3}; // set difference
}