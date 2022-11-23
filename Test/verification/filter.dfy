// RUN: %baredafny verify %args --boogie-filter='*Succeeds*' --bprint:"%t.bpl" %s > %t
// RUN: ! %baredafny verify %args %s >> %t
// RUN: %diff "%s.expect" "%t"

method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
}
