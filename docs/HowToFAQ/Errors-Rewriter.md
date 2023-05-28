
<!-- %check-resolve %default %useHeadings -->


<!-- FILE ./DafnyCore/Rewriters/TimeLimitRewriter.cs -->

## **Warning: timeLimitMultiplier annotation overrides timeLimit annotation** {#rw_timelimit_multiplier}

<!-- %check-resolve-warn -->
```dafny
method {:timeLimitMultiplier 10} {:timeLimit 5} m() {}
```

The {:timeLimitMultiplier n} attribute tells the prover to use a time limit that is the given number
times the time limit otherwise specified by the options. The {:timeLimit n} attribute simply sets a new
value for the time limit. It does not make sense to have both attributes on the same declaration. 
One or the other should be removed. If they are both present, just the {:timeLimitMultiplier} is used.

<!-- ./DafnyCore/Rewriters/LocalLinter.cs -->

## **Warning: Argument to 'old' does not dereference the mutable heap, so this use of 'old' has no effect**  {#rw_old_argument_not_on_heap}

<!-- %check-resolve-warn -->
```dafny
method m(i: int) 
{
   var j: int;
   j := 1;
   label L:
   j := 2;
   ghost var k := old@L(j);   
}
```

The `old` function, used in specifications and ghost code, indicates that the argument (an expression) 
is to be evaluated in some previous heap state. So if the argument does not depend on the heap, the `old` 
has no effect and is likely to lead to misunderstanding. Consequently, Dafny warns against doing so.
For example, it has no effect to apply `old` to a local variable; instead one should capture
the value of the local variable in a previous state using an otherwise unused ghost variable.

## **Warning: You have written an assert statement with a negated condition, but the lack of whitespace between 'assert' and '!' suggests you may be used to Rust and have accidentally negated the asserted condition. If you did not intend the negation, remove the '!' and the parentheses; if you do want the negation, please add a space between the 'assert' and '!'." {#rw_warn_negated_assertion}

```dafny
method m() {
  assert!(1 == 1);
}
```

This message warns about a common syntax error for people familiar with Rust. 
In Rust `assert! e` indicate checking that expression `e` holds. But in Dafny teh `!` negates the expression.
That is `assert! e` is `assert `!e`. The syntactic solution to avoiud the warning is to either put space 
between the `assert` and `!` (if the negation is intended) or to omit the `!` (if the negation is not intended.

<!-- FILE ./DafnyCore/Rewriters/InductionRewriter.cs-->

## **Warning: _item_s given as :induction arguments must be given in the same order as in the quantifier; ignoring attribute** {#rw_induction_arguments_quantifier_mismatch}

<!-- %check-resolve-warn -->
```dafny
predicate g(i: int, j: int)
function f(): int
  ensures forall i: int, j: int {:induction j,i} | true :: g(i,j)
{ 0 }
```

The `{:induction}` attribute gives some guidance to the prover as to how to construct the induction argument that 
proves the lemma. The heuristics that infer an induction proof require that the arguments of the attribute be in the
same order as the bound variables of the quantifier. If not, the :induction attribute is ignored.

## **Warning: lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute** {#rw_induction_arguments_lemma_mismatch}

<!-- %check-resolve-warn -->
```dafny
lemma {:induction j,i} m(i: int, j: int) ensures i + j == j + i {}
```

The `{:induction}` attribute gives some guidance to the prover as to how to construct the induction argument that 
proves the lemma. The heuristics that infer an induction proof require that the arguments of the attribute be in the
same order as the parameters of the lemma. If not, the :induction attribute is ignored.

## **Warning: invalid :induction attribute argument; expected _what_; ignoring attribute** {#rw_invalid_induction_attribute}

<!-- %check-resolve-warn -->
```dafny
lemma {:induction 42} m(i: int, j: int) ensures i + j == j + i {} 
```

The arguments of the `:induction` attribute can be any of the lemma parameters (for a lemma)
or bound quantifiers (for a quantifier expression), the `this` keyword, or true or false.

<!-- FILE ./DafnyCore/Rewriters/ConstructorWarning.cs -->

## **Warning: Constructor name '_pattern_' should be followed by parentheses** {#rw_warn_constructor_parentheses}

<!-- %check-resolve-warn %options --warn-missing-constructor-parentheses -->
```dafny
datatype D = A | B

method m(d: D) {
  match d {
    case A => return;
    case B() => return;
  }
}
```

The pattern following a `case` keyword can be a constructor possibly without arguments or it can be 
new variable to be bound to the match expression. A parameter-less constructor may be written
without parentheses. A simple identifier that happens to be a constructor of right type 
will be matched in preference as the constructor.

This can lead to surprises if there is a matching constructor that the writer or the reader of the
software is unaware of. So it is useful to always write constructors with parentheses, to visually
distinguish them from simple identifiers.

The `--warn-missing-constructor-parentheses` option will warn if a constructor is used without
parentheses. The solution is to either add parentheses (if a constructor is intended) or
rename the identifier (if a fresh bound identifier is intended).

<!-- FILE ./DafnyCore/RewritersPrecedenceLinter.cs-->

## **Warning: unusual indentation in _what_ (which starts at _location_); do you perhaps need parentheses?** {#rw_unusual_indentation_start}

<!-- %check-resolve-warn -->
```dafny
function f(b: bool): bool
{
  b &&
  b ==> b // this parses as (b && b) ==> b, but reads as b && (b ==> b)
}
```

Long expressions are best split up across multiple lines; readers often use indentation as a guide
to the nesting of subexpressions. For example, parallel conjuncts or disjuncts may be written with 
the same indentation. This warning occurs when the observed indentation is likely to cause
a misunderstanding of the code, particularly of the precedence of operations. It is suggested
to use parentheses or to redo the indentation to make the structure of the expression clearer.

## **Warning: unusual indentation in _what_ (which ends at _location_); do you perhaps need parentheses?** {#rw_unusual_indentation_end}

<!-- %check-resolve-warn -->
```dafny
function f(b: bool): bool
{
  b ==> b && 
  b          // this parses as b ==> (b && b), but reads as (b ==> b) && b
}
```

Long expressions are best split up across multiple lines; readers often use indentation as a guide
to the nesting of subexpressions. For example, parallel conjuncts or disjuncts may be written with 
the same indentation. This warning occurs when the observed indentation is likely to cause
a misunderstanding of the code, particularly of the precedence of operations. It is suggested
to use parentheses or to redo the indentation to make the structure of the expression clearer.

