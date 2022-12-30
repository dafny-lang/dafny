// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate IsLessThanSuccesor(i:int)
{
  i < i + 1
}

lemma LemmaWithoutTriggerOnForallStatement()
{
  forall i
    ensures IsLessThanSuccesor(i);
  {
  }
}





