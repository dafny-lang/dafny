// RUN: %dafny /showSnippets:1 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate Test(y: int) {
  y >= 1
}

method f(b: bool) returns (y: int)
  ensures Test(y)
{
  y := 0;
}

method g(b: bool, test: seq<bool>) returns (y: int)
  ensures 0 <= y < |test| ==> test[y]
{
  y := 0;
}

method h() {
  Never();
}

method Never()
  requires 1 == 0
{
}