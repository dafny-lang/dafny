// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  SwingoutSister();
}

method SwingoutSister() {
  break Out;
}
