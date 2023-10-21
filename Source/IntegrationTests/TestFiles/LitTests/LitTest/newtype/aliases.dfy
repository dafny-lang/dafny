// RUN: %baredafny resolve --use-basename-for-filename %s > %t
// RUN: %diff "%s.expect" %t

newtype VerySpecificInt = x : SpecificIntAlias | x == 1 witness 1
type SpecificIntAlias = SpecificInt
newtype SpecificInt = x : int | 0 <= x <= 10