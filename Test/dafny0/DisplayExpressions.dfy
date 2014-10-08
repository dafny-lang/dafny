// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method M()
{
  var m := map[];  // error: underspecified type
}

method N()
{
  var n := multiset{};  // error: underspecified type
}

method O()
{
  var o := [];  // error: underspecified type
}

method P()
{
  var p := {};  // error: underspecified type
}

method Q()
{
  assert (((map[]))) == (((((map[])))));  // error (but not 10 errors)
}
