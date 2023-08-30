// RUN: %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(z: int, i: int, j: int, k: int) 

ghost predicate ComplexPredicate3(offset: int, j: int, i: int)
{
  && (forall k :: P(1+offset, i, j, k) || P(0, i, j, k))
  && (forall k :: P(2+offset, i, j, k) || P(1, i, j, k))
  && (forall k :: P(3+offset, i, j, k) || P(2, i, j, k))
  && (forall k :: P(4+offset, i, j, k) || P(3, i, j, k))
  && (forall k :: P(5+offset, i, j, k) || P(4, i, j, k))
  && (forall k :: P(6+offset, i, j, k) || P(5, i, j, k))
  && (forall k :: P(7+offset, i, j, k) || P(6, i, j, k))
  && (forall k :: P(8+offset, i, j, k) || P(7, i, j, k))
  && (forall k :: P(9+offset, i, j, k) || P(8, i, j, k))
  && (forall k :: P(0+offset, i, j, k) || P(9, i, j, k))
}

ghost predicate ComplexPredicate2(offset: int, i: int)
{
  && ComplexPredicate3(offset, i, 0)
  && ComplexPredicate3(offset, i, 1)
  && ComplexPredicate3(offset, i, 2)
  && ComplexPredicate3(offset, i, 3)
  && ComplexPredicate3(offset, i, 4)
  && ComplexPredicate3(offset, i, 5)
  && ComplexPredicate3(offset, i, 6)
  && ComplexPredicate3(offset, i, 7)
  && ComplexPredicate3(offset, i, 8)
  && ComplexPredicate3(offset, i, 9)
}

ghost predicate ComplexPredicate1(offset: int)
{
  && ComplexPredicate2(offset, 0)
  && ComplexPredicate2(offset, 1)
  && ComplexPredicate2(offset, 2)
  && ComplexPredicate2(offset, 3)
  && ComplexPredicate2(offset, 4)
  && ComplexPredicate2(offset, 5)
  && ComplexPredicate2(offset, 6)
  && ComplexPredicate2(offset, 7)
  && ComplexPredicate2(offset, 8)
  && ComplexPredicate2(offset, 9)
}

ghost predicate ComplexPredicate0()
{
  && ComplexPredicate1(0)
  && ComplexPredicate1(1)
  && ComplexPredicate1(2)
  && ComplexPredicate1(3)
  && ComplexPredicate1(4)
  && ComplexPredicate1(5)
  && ComplexPredicate1(6)
  && ComplexPredicate1(7)
  && ComplexPredicate1(8)
  && ComplexPredicate1(9)
}

lemma {:autoRevealDependencies 1} StressForDafny()
  requires ComplexPredicate0()
  ensures ComplexPredicate1(0) 
  && ComplexPredicate1(1)
  && ComplexPredicate1(2)
  && ComplexPredicate1(3)
  && ComplexPredicate1(4)
  && ComplexPredicate1(5)
{
}