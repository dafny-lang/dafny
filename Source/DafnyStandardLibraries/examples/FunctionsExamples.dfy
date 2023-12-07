module FunctionExamples {

  import opened Std.Functions

  const square := (x: int) => x * x
  lemma TestInjective()
    ensures Injective<int, int>((x) => x + 2)
    ensures !Injective<int, int>((x) => x * x)
  {
    assert square(-1) == square(1);
  }

  const subtract := (x: int, y: int) => x - y
  lemma TestCommutative()
    ensures Commutative<int, int>((x, y) => x + y)
    ensures !Commutative<int, int>(subtract)
  {
    assert subtract(1,2) != subtract(2,1);
  }

  lemma TestAssociative()
    ensures Associative<int>((x, y) => x + y)
    ensures !Associative<int>(subtract)
  {
    assert subtract(1,2) != subtract(2,1);
  }

}