// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This method can be used to test compilation.
ghost method M()
{
   ghost var im := imap[2:=3];
   // test "in"
   if(2 in im)
   {
   }
   else
   { assert false; }
   // test "!in"
   if(3 !in im)
   {
   }
   else
   { assert false; }
   // dereference
   if(im[2] == 3)
   {
   }
   else
   { assert false; }
   // test applicative nature of Map<U, V> in C#
   if(im == imap[2 := 3])
   {
   }
   else
   { assert false; }
}

lemma m()
{
   ghost var a := imap i | i == 2 :: 3; var b := imap i | i == 3 :: 2;
   assert a[b[3]] == 3;
}
lemma m2(a: imap<int, bool>, b: imap<int, bool>)
   requires forall i | 0 <= i < 100 :: i in a && i in b && a[i] != b[i];
{
   assert forall i | 0 <= i < 100 :: a[i] || b[i];
}
lemma m3(a: imap<int, int>)
   requires forall i | 0 <= i < 100 :: i in a && a[i] == i*i;
{
   assert a[20] == 400;
}
lemma m4()
{
   ghost var a := imap i | i == 3 :: 9;
   if(a[4] == 4) // UNSAFE, 4 not in the domain
   {
      m();
   }
}

lemma m5(a: imap<int, int>)
   requires 20 in a;
{
   assert a[20] <= 0 || 0 < a[20];
}
lemma m7()
{
   var a := imap[1:=1, 2:=4, 3:=9];
   assert forall i | i in a :: a[i] == i * i;
   assert 0 !in a;
   assert 1 in a;
   assert 2 in a;
   assert 3 in a;
   assert forall i | i < 1 || i > 3 :: i !in a;
}
function Update<K, V>(a:imap<K, V>, k:K, v:V):imap<K, V>
{// imap j | (j == k || j in a) :: (if j == k then v else a[j])
    imap j | j in iset{k} + a.Keys :: (if j == k then v else a[j])
}
method m8()
{
   ghost var a: imap<int,int> := imap i | false :: 0;
   assert forall i :: i !in a; // check emptiness
   var i,n := 0, 100;
   while(i < n)
      invariant 0 <= i <= n;
      invariant forall i | i in a :: a[i] == i * i;
      invariant forall k :: 0 <= k < i <==> k in a;
   {
      a := Update(a, i, i * i);
      i := i + 1;
   }
   m3(a);
}
lemma m12()
{
   ghost var x := imap i | 0 <= i < 10 :: i * 2;
   assert 0 in x;
   assert 1 in x;
   assert 10 !in x;
   assert x[0] == 0 && x[2] == 4;
}

/*
function domain<U, V>(m: imap<U,V>): set<U>
   ensures forall i :: i in domain(m) <==> i in m;
{
   set s | s in m // UNSAFE, m may have infinite domain
}
*/

method m13()
{
   var s := {0, 1, 3, 4};
   ghost var x := imap i | i in s :: i;
   assert forall i | i in x :: x[i] == i;
//   assert domain(x) == s;
}

class A { var x: int; }

method m15(b: set<A>)
{
  ghost var m := imap a | a in b :: a.x;
  var aa := new A;
  assert aa !in m;
}


method minf()
{
  ghost var m := imap i | i > 100 :: 2 * i;
  assert 101 in m;
  assert 99 !in m;
  assert m[101] == 202;
  assert forall i :: i > 200 ==> m[i] == 2 * i;
}
