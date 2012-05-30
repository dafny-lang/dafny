
// This method can be used to test compilation.
method Main()
{
   var m:= map{2:=3};
   // test "in"
   if(2 in m)
   {
      print "m0\n";
   }
   else
   { assert false; }
   // test "!in"
   if(3 !in m)
   {
      print "m1\n";
   }
   else
   { assert false; }
   // dereference
   if(m[2] == 3)
   {
      print "m2\n";
   }
   else
   { assert false; }
   // test disjoint operator
   if(m !! map{3 := 3})
   {
      print "m3\n";
   }
   else
   { assert false; }
   // updates should replace values that already exist
   if(m[2 := 4] == map{2 := 4})
   {
      print "m4\n";
   }
   else
   { assert false; }
   // add something to the map
   if(m[7 := 1] == map{2 := 3,7 := 1})
   {
      print "m5\n";
   }
   else
   { assert false; }
   // test applicative nature of Map<U, V> in C#
   if(m == map{2 := 3})
   {
      print "m6\n";
   }
   else
   { assert false; }
   // this should print all m1, m2, ... m6.
}

method m()
{
   var a := map{2:=3}; var b := map{3:=2};
   assert a[b[3]] == 3;
}
method m2(a: map<int, bool>, b: map<int, bool>)
   requires forall i | 0 <= i < 100 :: i in a && i in b && a[i] != b[i];
{
   assert forall i | 0 <= i < 100 :: a[i] || b[i];
}
method m3(a: map<int, int>)
   requires forall i | 0 <= i < 100 :: i in a && a[i] == i*i;
{
   assert a[20] == 400;
}
method m4()
{
   var a := map{3 := 9};
   if(a[4] == 4) // UNSAFE, 4 not in the domain
   {
      m();
   }
}

method m5(a: map<int, int>)
   requires 20 in a;
{
   assert a[20] <= 0 || 0 < a[20];
}
method m6()
{
   var a := map{3 := 9};
   assert a[3:=5] == map{3:=5};
   assert a[2:=5] == map{2:=5, 3:=9};
   assert a[2:=5] == map{2:=6, 3:=9, 2:=5}; // test the ordering of assignments in the map literal
}
method m7()
{
   var a := map{1:=1, 2:=4, 3:=9};
   assert forall i | i in a :: a[i] == i * i;
   assert 0 !in a;
   assert 1 in a;
   assert 2 in a;
   assert 3 in a;
   assert forall i | i < 1 || i > 3 :: i !in a;
}
method m8()
{
   var a := map{};
   assert forall i :: i !in a; // check emptiness
   var i,n := 0, 100;
   while(i < n)
      invariant 0 <= i <= n;
      invariant forall i | i in a :: a[i] == i * i;
	  invariant forall k :: 0 <= k < i <==> k in a;
   {
      a := a[i := i * i];
      i := i + 1;
   }
   assert a !! map{-1:=2};
   m3(a);
}
method m9()
{
   var a, b := map{}, map{};
   assert a !! b;
   b := map{2:=3,4:=2,5:=-6,6:=7};
   assert a !! b;
   assert b !! map{6:=3}; // ERROR, both share 6 in the domain.
}
method m10()
{
   var a, b := map{}, map{};
   assert a !! b;
   b := map{2:=3,4:=2,5:=-6,6:=7};
   assert a !! b;
   a := map{3:=3,1:=2,9:=-6,8:=7};
   assert a !! b;
}
method m11<U, V>(a: map<U, V>, b: map<U, V>)
   requires forall i :: !(i in a && i in b);
{
   assert a !! b;
}
