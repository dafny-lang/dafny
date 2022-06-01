// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/quantifierSyntax:4"} NewSyntax {
  method M()
  {
    var _ := set x <- 5;
    var _ := set x: int | 0 <= x < 10, y | "true" :: y;
    var _ := set x <- [3], y | "true" :: y;
    
    // var numbers := [0, 1, 2, 3];
    // var _ := set x <- numbers | 0 < x, y | y == 6 / x :: y;
  }
}