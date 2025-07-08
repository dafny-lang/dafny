// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --show-proof-obligation-expressions

method Termination(start: int, up: bool) {
    for i := start downto *
      invariant start - 768 < i
      decreases i - start + 765 // error: not bounded below
    {
      if i == start - 768 {
        return;
      }
    }
}
