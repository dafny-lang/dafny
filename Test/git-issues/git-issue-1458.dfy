// RUN: %dafny_0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  SwingoutSister();
}

method SwingoutSister() {
  break Out;
}
