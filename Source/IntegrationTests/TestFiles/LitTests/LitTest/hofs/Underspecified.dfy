// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Underspecified() {
  // all these have underspecified types, which is not ok
  var u := _ => 0;
  var v := (_, _) => 0;
  var w := a => a;
}

