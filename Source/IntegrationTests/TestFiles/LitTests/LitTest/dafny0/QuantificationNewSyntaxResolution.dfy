// RUN: %exits-with 2 %build --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/quantifierSyntax:4"} NewSyntax {
  method M()
  {
    // Ensuring we get sensible errors for type mismatches,
    // despite the current desugaring implementation.
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


    // Dealing with the ambiguity of "<-": we parse it as two separate tokens
    // but shouldn't allow whitespace in between when it is used as a single token.
    var c := [1, 2, 3];
    var _ := set x <- c;  // Allowed
    var _ := set x < - c; // Error: arguments to < must have a common supertype (got set<?> and seq<int>)
                          // Error: type of unary - must be of a numeric or bitvector type (instead got seq<int>)
  }
}