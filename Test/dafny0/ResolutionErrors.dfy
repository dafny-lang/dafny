method UmmThisIsntGoingToWork()
{
   var a := new int [2];
   var b := new int [1];
   a[0] := 1;
   a[1] := -1;

   ghost var i := 0;
   while (i < 2)
      decreases *;  // error: not allowed on a ghost loop
      invariant i <= 2;
      invariant forall j :: 0 <= j && j < i ==> a[j] > 0;
   {
      i := 0;
   }
   assert a[1] == -1;  // ...for then this would incorrectly verify
   b[a[1]] := 0;
}
