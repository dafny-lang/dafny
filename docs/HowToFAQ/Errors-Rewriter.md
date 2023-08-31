
<!-- %check-resolve %default %useHeadings %check-ids -->

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

## **Warning: Argument to 'old' does not dereference the mutable heap, so this use of 'old' has no effect** {#rw_old_argument_not_on_heap}

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

## **Warning: You have written an assert statement with a negated condition, but the lack of whitespace between 'assert' and '!' suggests you may be used to Rust and have accidentally negated the asserted condition. If you did not intend the negation, remove the '!' and the parentheses; if you do want the negation, please add a space between the 'assert' and '!'.** {#rw_warn_negated_assertion}

<!-- %check-resolve-warn -->
```dafny
method m() {
  assert!(1 == 1);
}
```

This message warns about a common syntax error for people familiar with Rust. 
In Rust `assert! e` indicates checking that expression `e` holds. But in Dafny the `!` negates the expression.
That is `assert! e` is `assert !e` in Dafny. The syntactic solution to avoid the warning is to either put space 
between the `assert` and `!` (if the negation is intended) or to omit the `!` (if the negation is not intended).

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

<!-- TODO - not sure this is reachable -->

The `{:induction}` attribute gives some guidance to the prover as to how to construct the induction argument that 
proves the lemma. The heuristics that infer an induction proof require that the arguments of the attribute be in the
same order as the parameters of the lemma. If not, the :induction attribute is ignored.

## **Warning: invalid :induction attribute argument; expected _what_; ignoring attribute** {#rw_invalid_induction_attribute}

<!-- %check-resolve-warn -->
```dafny
const c := 0
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

<!-- FILE ./DafnyCore/Rewriters/RunAllTestsMainMethod.cs -->

## **Error: Methods with the :test attribute may not have input arguments** {#rw_test_methods_may_not_have_inputs}

<!-- %check-test -->
```dafny
method {:test} m(i: int) {}
```

The test tool runs all the methods that are marked with `{:test}`. The test tool expects two kinds of
behavior: (a) the method may abort with a failing `expect` or (b) the method may return a datatype value that
has an `IsFailure()` function which returns false. But the test method has no means of selecting inputs to
give to a method under test. An experimental test-generation tool is in development, but for the moment, a
routine under test may not have input arguments. A typical solution is to write an auxiliary method,
marked with `{:test}`, that takes no
inputs, and that then calls the desired method with various combinations of inputs.

## **Error: Methods with the :test attribute can have at most one return value** {#rw_test_method_has_too_many_returns}

<!-- %check-test -->
```dafny
method {:test} m() returns (j: int, k: int) 
{
  j, k := 0,0;
}
```

This error only occurs when using `dafny test`. That command executes all methods attributed
with `{:test}`, but such test methods are limited to methods with at most one output parameter.
Typically that out-parameter has a failure-compatible type whose value is used to indicate whether the 
test succeeeded or failed. If the type is not a failure-compatible type, the test is presumed to be successful.
This is purely an implementation limitation. (cf. [Issue 3387](https://github.com/dafny-lang/dafny/issues/3387))

<!-- FILE ./DafnyCore/Rewriters/ExpectContracts.cs-->

## **Warning: The _kind_ clause at this location cannot be compiled to be tested at runtime because it references ghost state.** {#rw_clause_cannot_be_compiled}

<!-- %no-check %check-test %options --test-assumptions:Externs -->
```dafny
method {:extern} m(i: int, ghost j: int) 
  requires j == 1
```

The `--test-assumptions` option inserts tests of various contracts and implicit assumptions 
in a Dafny method, such as the requires and ensures clauses.
However, because these inserted tests are compiled into the target
program as runtime checks, they cannot refer to any ghost variables.
(This mechanism implements Dafny's runtime-assertion checking.)
 
## **Warning: Internal: no wrapper for _name_** {#rw_no_wrapper}

This message indicates a bug within the `dafny` tool. Please report the program that
triggered the message to [the Github issues site](https://www.github.com/dafny-lang/dafny/issues).

## **Warning: No :test code calls _name_** {#rw_unreachable_by_test}

This warning indicates that some method marked with {:extern} is not called
by any method marked with {:test}. The intention is to check coverage of
the programmed unit tests. The warning only appears when using
`/testContracts:TestedExterns` with the legacy CLI.
It is likely to be removed in a future version of `dafny`.

<!-- FILE ./DafnyCore/Rewriters/PrintEffectEnforcement.cs-->

## **Error: :print attribute is not allowed on functions** {#rw_print_attribute_forbidden_on_functions}

<!-- %check-resolve -->
```dafny
function {:print} f(): int { 0 }
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
Thus Dafny forbids (ghost or compiled) functions from declaring that they have
a print side-effect (whether or not print effects are being tracked with 
`--track-print-effects`).

## **Error: :print attribute is not allowed on ghost methods** {#rw_print_attribute_forbidden_on_ghost_methods}

<!-- %check-resolve -->
```dafny
ghost method {:print} f() { }
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
A program's ghost code is not allowed to modify the actual execution of a program.
Thus ghost code should not contain print statements.
So Dafny forbids ghost methods from declaring that they have a print side-effect
(whether or not print effects are being tracked with `--track-print-effects`).

## **Error: not allowed to override a non-printing method with a possibly printing method (_name_)** {#rw_override_must_preserve_printing}

<!-- %check-resolve -->
```dafny
trait T {
  method m()
}

class C extends T {
  method {:print} m() {}
}
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
If a trait declares a method without a `{:print}` attribute, then any implementation 
of that method may not do any printing, as it must obey the trait's specification.
Thus a class implementing that method by an override cannot declare the method as possibly
printing something, by giving it a `{:print}` attribute --- even if it does not actually do any printing.

## **Error: :print attribute does not take any arguments** {#rw_print_attribute_takes_no_arguments}

<!-- %check-resolve -->
```dafny
method {:print 42} f() { }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something.
No arguments to the attribute are needed or allowed.

## **Error: a function-by-method is not allowed to use print statements** {#rw_no_print_in_function_by_method}

<!-- %check-resolve %options --track-print-effects -->
```dafny
function f(): int {42 }
by method {
  print "I'm here\n";
  return 42;
}
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
A function-by-method has a method body that is intended to be a compiled way of computing 
what the function body expresses. But as a function may not have side-effects,
the method body should not have any print statements.

This tracking of print statements (and the forbidding of them by this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.

## **Error: to use a print statement, the enclosing _method_ must be marked with {:print}** {#rw_print_attribute_required_to_print}

<!-- %check-resolve %options --track-print-effects -->
```dafny
method m() { print 42; }
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
So a method that prints something (even transitively) should be marked with `{:print}`.
This error indicates that such an attribute is missing -- either add the attribute 
or remove the print statement.

This tracking of print statements (and thus the possibility of this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.

## **Error: a function-by-method is not allowed to call a method with print effects** {#rw_function_by_method_may_not_call_printing_method}

<!-- %check-resolve %options --track-print-effects -->
```dafny
function m(): int { 42 }
by method { p(); return 42; }

method {:print} p() {}
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
A function-by-method has a method body that is intended to be a compiled way of computing 
what the function body expresses. But as a function may not have side-effects,
the method body should not have any print statements.

In this case, the method body might print something because a method that is called in the body
is attributed with `{:print}` (whether or not it actually does print something).

This tracking of print statements (and thus the possibility of this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.

## **Error: to call a method with print effects, the enclosing _method_ must be marked with {:print}** {#rw_must_be_print_to_call_printing_method}

<!-- %check-resolve %options --track-print-effects -->
```dafny
method m() { p(); }

method {:print} p() {}
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
In this case, the method body might print something because a method that is called in the body
is attributed with `{:print}` (whether or not it actually does print something).
So the calling method must be marked with `{:print}` as well.

This tracking of print statements (and thus the possibility of this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.
