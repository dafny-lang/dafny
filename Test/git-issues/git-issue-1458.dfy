// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  SwingoutSister();
}

method SwingoutSister() {
  break Out;
}
