
method testing1() 
{
   var a, b, c := {1,2}, {3, 4}, {5, 6};
   assert a !! b !! c;
   testing2(a, b, c);
   assert !({1,2} !! {2,3});
   assert !({1,2} !! {9} !! {2,3}); // tests the accumulation
   assert !({1,2} !! {9} !! {2,3});
   assert !({1,2} !! {9} !! {8} !! {2,3}); // doesn't break at 4. that seems like a good stopping place.
   assert !({9} !! {1,2} !! {8} !! {2,3});
   assert !({9} !! {1} + {2} !! {8} !! {2,3}); // mixing in some other operators
   assert !({1} !! {1} + {2});
}

method testing2(a: set<int>, b: set<int>, c: set<int>)
   requires a !! b !! c;
{
   assert a !! b;
   assert a !! c;
   assert b !! c;
}

method testing3(a: set<int>, b: set<int>, c: set<int>, d: set<int>) // again with the four.
   requires a !! b !! c !! d;
{
   assert a !! b;
   assert a !! c;
   assert b !! c;
   assert a !! d;
   assert b !! d;
   assert c !! d;
}
