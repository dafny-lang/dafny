// RUN: ! %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: int)
predicate G(x: int)

lemma SplitIntoConjunctOfForalls(x: int) 
  ensures P(x)
  ensures G(x)
{
  forall y: int {:trigger P(y), G(y)} 
  {
    SplitIntoConjunctOfForalls(y + 1);
  }
}