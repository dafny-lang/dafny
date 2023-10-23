// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type IntMap = map<int, int>

ghost function RemoveElement(m: IntMap, x: int): IntMap
{
  // The following operation once got resolved as set difference instead
  // of map domain subtraction, because the resolver didn't expand the
  // IntMap type synonym before checking if the type was a map.
  m - {x}
}

ghost function RemoveElement'(m: map<int, int>, x: int): map<int, int>
{
  // This operation always worked (and continues to work)
  m - {x}
}
