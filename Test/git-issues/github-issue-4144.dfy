// RUN: %baredafny resolve %s > %t
// RUN: %diff "%s.expect" "%t"

module P {
  predicate m() reads {} 
} 
module Q refines P {
  predicate m() { true }
}