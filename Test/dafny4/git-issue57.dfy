// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma lemma_RotateRightAdds(x:bv32)
   ensures  (x.RotateRight(2)).RotateRight(3) == x.RotateRight(5);
{
}


