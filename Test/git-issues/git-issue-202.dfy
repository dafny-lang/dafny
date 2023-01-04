// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method push<T>(sequence: seq<T>, element: T) returns (new_sequence: seq<T>)
  ensures sequence == new_sequence[..|new_sequence|-1]
{
  return sequence + [element];
}
