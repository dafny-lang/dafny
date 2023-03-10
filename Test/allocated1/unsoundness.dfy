// RUN: %dafny /allocated:1 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The mode /allocated:1 is not sound, as is demonstrated by this test file.

class Class { var data: int }

ghost function F(): set<Class>
{
  set c: Class | allocated(c)
}

method M()
  ensures false  // verifies! :O
{
  ghost var x := F();
  assert forall u :: u in x ==> allocated(u);
  var c := new Class;
  ghost var y := F();
  assert x == y;

  assert !old(allocated(c));  // because c was newly allocated
  assert c in x;
  assert old(allocated(c));  // because c in x
}
