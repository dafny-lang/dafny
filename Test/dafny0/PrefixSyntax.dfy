// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype TextProcessing =
  | TeX    // prefix |
  | LaTeX
  | Madoko

predicate InfixStyle(x: int, y: int, t: TextProcessing)
{
  (t == TeX ==> x < y) &&
  (t == LaTeX || t == TeX ==> x == 100 && y == 1000) &&
  (t == Madoko ==> 0 <= x || 0 <= y)
}

predicate TLA_plus_Style(x: int, y: int, t: TextProcessing)
{
  // This expression is semantically the same as the one in InfixStyle
  && (t == TeX ==> x < y)
  && (|| t == LaTeX
      || t == TeX
    ==>
     && x == 100
     && y == 1000
     )
  && (t == Madoko ==> || 0 <= x || 0 <= y)
}

lemma Same(x: int, y: int, t: TextProcessing)
  ensures InfixStyle(x, y, t) == TLA_plus_Style(x, y, t)
{
}

datatype MyRecord = | MakeItHere(z: int)

function UnitConjunct(y: int): bool
{
  && y == 5
}

function UnitDisjunct(y: int): bool
{
  || y == 5
}

lemma Units(y: int)
  ensures UnitConjunct(y) == UnitDisjunct(y)
{
}

function MyPredicate(y: int): bool
{
  // the <==> in the following line has lower precedence than the unit disjunnctions
  || 5 + y == 0 <==> && 10 + y == 0
}


function MyPredicateClean(y: int): bool
{
  5 + y == 0 <==> 10 + y == 0
}

lemma MyPred(y: int)
  ensures MyPredicate(y) == MyPredicateClean(y)
{
}

lemma CheckMyPred_0(y: int)
  requires MyPredicate(y)
  ensures y != -5 && y != -10
{
}

lemma CheckMyPred_1(y: int)
  ensures MyPredicate(4)
{
}
