// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma LemmaOutsideofScaffolding2(a: int, b: int)
  ensures a == b
{
  assert false;
}

lemma LemmaWithScaffolding()
{
  assert {:only "after"} true;
}

lemma LemmaOutsideofScaffolding(a: int, b: int)
  ensures a == b
{
  assert false;
}