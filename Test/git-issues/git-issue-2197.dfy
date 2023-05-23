// RUN: %exits-with 4 %baredafny /compile:0 /showSnippets:1 "%s" > "%t".raw
// RUN: %sed 's/^.*[\/\\]//' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate Test(y: int) {
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
