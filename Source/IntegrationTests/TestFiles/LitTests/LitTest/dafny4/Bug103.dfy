// RUN: %testDafnyForEachResolver "%s"


ghost predicate IsLessThanSuccesor(i:int)
{
  i < i + 1
}

lemma LemmaWithoutTriggerOnForallStatement()
{
  forall i
    ensures IsLessThanSuccesor(i)
  {
  }
}





