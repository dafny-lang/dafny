// RUN: %testDafnyForEachResolver "%s" --expect-exit-code=2

class Stack<T(0)> {
}

class Stack<T(0)> {
  ghost var s: seq<T>

  method Pop() returns (v: T)
    ensures v == old(s[0]) && s == old(s[1..])
}