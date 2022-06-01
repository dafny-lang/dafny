// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/quantifierSyntax:4"} NewSyntax {
  method M()
  {
    var _ := set x <- 5;
    var _ := set x <- [5], y <- 5 :: y;
    var _ := set x: int | 0 <= x < 10, y | "true" :: y;
    var _ := set x <- [3], y | "true" :: y;
    var _ := set x, y | "true" :: y;

    var _ := map x <- 5 :: x + 2;
    var _ := map x <- [5], y <- 5 :: x := y;
    var _ := map x: int | 0 <= x < 10, y | "true" :: x := y;
    var _ := map x <- [3], y | "true" :: x := y;
    var _ := map x, y | "true" :: x := y;

    var _ := forall x <- 5 :: x < 10;
    var _ := forall x <- [5], y <- 5 :: x < 10;
    var _ := forall x: int | 0 <= x < 10, y | "true" :: x < 10;
    var _ := forall x <- [3], y | "true" :: x < 10;
    var _ := forall x, y | "true" :: x < 10;

    var _ := exists x <- 5 :: x < 10;
    var _ := exists x <- [5], y <- 5 :: x < 10;
    var _ := exists x: int | 0 <= x < 10, y | "true" :: x < 10;
    var _ := exists x <- [3], y | "true" :: x < 10;
    var _ := exists x, y | "true" :: x < 10;

    forall x <- 5 {}
    forall x <- [5], y <- 5 {}
    forall x: int | 0 <= x < 10, y | "true" {}
    forall x <- [3], y | "true" {}
    forall x, y | "true" {}
  }
}