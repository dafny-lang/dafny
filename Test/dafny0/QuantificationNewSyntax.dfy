// RUN: %exits-with 4 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/quantifierSyntax:4"} NewSyntax {
  method M()
  {
    // Illustrating that per-quantified variable ranges
    // can be used to ensure later domains and ranges
    // are well-formed.
    var numbers := [0, 1, 2, 3];
    var _ := set x <- numbers, y | y == 6 / x :: y;         // Error: possible division by zero
    var _ := set x <- numbers | 0 < x, y | y == 6 / x :: y; // Success
    var _ := set x <- numbers, y <- F(x) :: y;          // Error: function precondition might not hold
    var _ := set x <- numbers | x < 3, y <- F(x) :: y;  // Success
    var _ := set x <- numbers | x < 3, y <- F(x) :: y as nat;          // Error: result of operation might violate subset type constraint for 'nat'
    var _ := set x <- numbers | x < 3, y <- F(x) | 0 <= y :: y as nat; // Success
  }

  function F(x: nat): seq<int> requires x < 3 {
    [-5, 4, 0, -12]
  }
}
