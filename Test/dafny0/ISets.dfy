// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost method M()
{
   ghost var s := iset{2};
   // test "in"
   if(2 in s)
   {
   }
   else
   { assert false; }
   // test "!in"
   if(3 !in s)
   {
   }
   else
   { assert false; }

   if(s == iset{2})
   {
   }
   else
   { assert false; }
}

ghost method m1() {
 var s1:iset<int> := iset{}; // the empty set
 var s2 := iset{1, 2, 3}; // set contains exactly 1, 2, and 3
 assert s2 == iset{1,1,2,3,3,3,3}; // same as before
 var s3, s4 := iset{1,2}, iset{1,4};

 assert s2 + s4 == iset{1,2,3,4}; // set union
 assert s2 * s3 == iset{1,2} && s2 * s4 == iset{1}; // set intersection
 assert s2 - s3 == iset{3}; // set difference

 assert (iset x | x in s2 :: x+1) == iset{2,3,4}; // set comprehension
 assert 17 in (iset x: int | true :: x); // set comprehension

 assert (imap x: int | true :: x+1)[14] == 15;
}


