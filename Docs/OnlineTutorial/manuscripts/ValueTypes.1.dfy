method()
{
   var s1 := {}; // the empty set
   var s2 := {1, 2, 3}; // set contains exactly 1, 2, and 3
   assert s2 == {1,1,2,3,3,3,3}; // same as before
   var s3, s4 := {1,2}, {1,4};
}