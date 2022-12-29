// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

least predicate Natural(x: int) {
  x == 0 || Natural(x - 1)
}

greatest predicate Positive(x: int) {
  x != 0 && Positive(x + 1)
}

least lemma NaturalIsNat(x: int)
  requires Natural(x)
  ensures 0 <= x
{
}

lemma NatIsNatural(x: int)
  requires 0 <= x
  ensures Natural(x)
{
}

lemma PositiveIsPos(x: int)
  requires x <= 0
  ensures !Positive(x)
  decreases -x
{
}

greatest lemma PosIsPositive(x: int)
  requires 0 < x
  ensures Positive(x)
{
}

lemma AboutNatural(x: int)
  ensures Natural(x) <==> 0 <= x
{
  if Natural(x) {
    NaturalIsNat(x);
  }
  if 0 <= x {
    NatIsNatural(x);
  }
}

lemma AboutPositive(x: int)
  ensures Positive(x) <==> 0 < x
{
  if 0 < x {
    PosIsPositive(x);
  } else {
    PositiveIsPos(x);
  }
}

method least(x: int, y: int) returns (least: int) {
  var greatest;
  least, greatest := mixmax(x, y);
}

method greatest(x: int, y: int) returns (greatest: int) {
  var least;
  least, greatest := mixmax(x, y);
}

method mixmax(x: int, y: int) returns (least: int, greatest: int)
  ensures {x, y} == {least, greatest}
  ensures least <= greatest
{
  if x < y {
    least, greatest := x, y;
  } else {
    least, greatest := y, x;
  }
}
