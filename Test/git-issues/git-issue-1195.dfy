// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M0(B: ORDINAL)
{
  var b := B;
  var w := 0 < b;
  var y := b.IsLimit;
}

method M1(B: ORDINAL)
{
  var b := B;
  var w := 0 <= b;
  var y := b.IsLimit; // this once had bogusly reported "type int does not have member IsLimit"
}
