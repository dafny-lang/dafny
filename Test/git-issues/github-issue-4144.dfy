// RUN: %baredafny resolve --use-basename-for-filename %s > %t
// RUN: %diff "%s.expect" "%t"

module P {
  predicate m() reads {}
  predicate p() reads []
  predicate q() reads multiset{}
} 
module Q refines P {
  predicate m() { true }
  predicate p() { true }
  predicate q() { true }
}