method m()
{
   var s := [1, 2, 3, 4, 5];
   assert [1,2,3] == [1] + [2,3];
   assert s == s + [];
   assert forall i :: 0 <= i <= |s| ==> s == s[..i] + s[i..];
}