// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"



method Main() {
  SwingoutSister();
}

method SwingoutSister() {
  break Out;
}
