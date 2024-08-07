// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D 
function f(d:D):bool {
  assert true by {
    match d {
      case _ => assert true;
    }
  }
  true
}