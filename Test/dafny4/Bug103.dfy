// RUN: %dafny /compile:0 /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate IsLessThanSuccesor(i:int)
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





