// RUN: %baredafny verify %args --bprint:"%t.bpl" --filter="Succeeds" %s > %t
// RUN: %baredafny verify %args %s >> %t || true
// RUN: %diff "%s.expect" "%t"

method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
}