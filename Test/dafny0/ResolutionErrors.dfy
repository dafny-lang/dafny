
//Should not verify, as ghost loops should not be allowed to diverge.
method GhostDivergentLoop()
{
   var a := new int [2];
   a[0] := 1;
   a[1] := -1;
   ghost var i := 0;
   while (i < 2)
      decreases *; // error: not allowed on a ghost loop
	  invariant i <= 2;
	  invariant (forall j :: 0 <= j && j < i ==> a[j] > 0);
   {
     i := 0;
   }
   assert a[1] != a[1]; // ...for then this would incorrectly verify
}

method M<T>(a: array3<T>, b: array<T>, m: int, n: int)
{
  // the following invalid expressions were once incorrectly resolved:
  var x := a[m, n];        // error
  var y := a[m];           // error
  var z := b[m, n, m, n];  // error
}
