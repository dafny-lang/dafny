// RUN: %verify --boogie-filter='*Succeeds*' --bprint:"%t.bpl" %s > %t
// RUN: ! %verify %s >> %t
// RUN: %diff "%s.expect" "%t"

method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
}
