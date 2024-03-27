// RUN: %resolve "%s" --allow-warnings > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  forall 
    ensures true 
  {
  }
}
