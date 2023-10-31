ghost predicate Injective<X(!new), Y>(f: X --> Y)
  reads f.reads
  requires forall x :: f.requires(x)
{
  forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
}