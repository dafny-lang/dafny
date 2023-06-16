// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Int = nat

method m(s: set<Int>) {
  var iter := s;
  while iter != {}
    decreases |iter|
  {
    var i: Int :| i in iter;
    iter := iter - {i};
  }
}
