module FunctionExamples {

  import opened DafnyStdLibs.Function

  lemma TestInjective() {
    assert Injective<int, int>((x) => x + 2);
    var square := (x: int) => x * x;
    assert square(-1) == square(1);
    assert !Injective<int, int>((x) => x * x);
  }

  lemma TestCommutative() {
    assert Commutative<int, int>((x, y) => x + y);
    var subtract := (x: int, y: int) => x - y;
    assert subtract(1,2) != subtract(2,1);
    assert !Commutative<int, int>(subtract);
  }

  lemma TestAssociative() {
    assert Associative<int>((x, y) => x + y);
    var subtract := (x: int, y: int) => x - y;
    assert subtract(1,2) != subtract(2,1);
    assert !Associative<int>(subtract);
  }

}