// RUN: %exits-with 2 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "--quantifier-syntax=3"} OldSyntax {
  method M()
  {
    var y := 5;
    print set x | 0 <= x < 10, y;       // Allowed, parsed as two separate arguments to print
    SomeMethod(set x | 0 <= x < 10, y); // Similarly

    var c := [1, 2, 3];
    print set x | 0 <= x < 10, y <- c;       // Allowed, parsed as two separate arguments to print (the second being "y <(- c)")
    SomeMethod(set x | 0 <= x < 10, y <- c); // Similarly

    // This is included because of the ambiguity of "<-" as either two separate tokens or one.
    // Generic instantiations can never use variance symbols so this should always be cleanly rejected.
    var _ := set x: SomeType<-T>;       // Error: invalid UnaryExpression
  }
}

module {:options "/quantifierSyntax:4"} NewSyntax {
  method M()
  {
    var y := 5;
    print set x | 0 <= x < 10, y;       // Error: a set comprehension with more than one bound variable must have a term expression
    SomeMethod(set x | 0 <= x < 10, y); // Error: a set comprehension with more than one bound variable must have a term expression

    var c := [1, 2, 3];
    print set x | 0 <= x < 10, y <- c;       // Error: a set comprehension with more than one bound variable must have a term expression
    SomeMethod(set x | 0 <= x < 10, y <- c); // Error: a set comprehension with more than one bound variable must have a term expression

    var _ := set x: SomeType<-T>;       // Error: invalid UnaryExpression
  }
}
