// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method M()
{
  var m := map[];
}

method N()
{
  var n := multiset{};
}

method O()
{
  var o := [];
}

method P()
{
  var p := {};
}
