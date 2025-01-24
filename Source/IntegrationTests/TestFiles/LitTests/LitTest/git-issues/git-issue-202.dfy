// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


method push<T>(sequence: seq<T>, element: T) returns (new_sequence: seq<T>)
  ensures sequence == new_sequence[..|new_sequence|-1]
{
  return sequence + [element];
}
