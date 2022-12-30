// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M() {
  var pos := 10;
  while (pos > 0) { // This shouldn't print int(pos) - int(0); pos - 0 would be better
    pos := pos - 1;
  }
}
