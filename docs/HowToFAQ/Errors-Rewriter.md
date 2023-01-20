
<!-- %check-resolve %default %useHeadings -->

<!-- ./DafnyCore/Rewriters/TimeLimitRewriter.cs -->

## **Warning: timeLimitMultiplier annotation overrides " + name + " annotation**

```ddafny
method {:timeLimitMultiplier 10} {:timeLimit 5} m() {}
```

The {:timeLimitMultiplier n} attribute tells the prover to use a time limit that is the given number
times the time limit otherwise specified by the options. The {:timeLimit n} attribute simply sets a new
value for the time limit. It does not make sense to have both attributes on the same declaration. 
One or the other should be removed.

<!-- ./DafnyCore/Rewriters/UselessOldLinter.cs -->

## **Warning: Argument to 'old' does not dereference the mutable heap, so this use of 'old' has no effect**

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


<!-- ./DafnyCore/Rewriters/InductionRewriter.cs-->

## **Warning: _item_s given as :induction arguments must be given in the same order as in the quantifier; ignoring attribute**

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

## **Warning: lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute**

<!-- %check-resolve-warn -->
```dafny
lemma {:induction j,i} m(i: int, j: int) ensures i + j == j + i {}
```

The `{:induction}` attribute gives some guidance to the prover as to how to construct the induction argument that 
proves the lemma. The heuristics that infer an induction proof require that the arguments of the attribute be in the
same order as the parameters of the lemma. If not, the :induction attribute is ignored.

## **Warning: invalid :induction attribute argument; expected _what_; ignoring attribute**

<!-- %check-resolve-warn -->
```dafny
lemma {:induction 42} m(i: int, j: int) ensures i + j == j + i {} 
```

The arguments of the `:induction` attribute can be any of the lemma parameters (for a lemma)
or bound quantifiers (for a quantifier expression), the `this` keyword, or true or false.

<!-- ./DafnyCore/Rewriters/ConstructorWarning.cs -->

## **Warning: Constructor name '_pattern_' should be followed by parentheses**

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
new variable to be bound to the match expression. A parameter-less costructor may be written
without parentheses. A simple identifier that happens to be a constructor of right type 
will be matched in preference to a new bound identifier.

This can lead to surprises if there is a matching constructor that the writer or the reader of the
software is unaware of. So it is useful to always write constructors with parentheses, to visually
distinguish them from simple identifiers.

The `--warn-missing-constructor-parentheses` option will warn if a constructor is used without
parentheses. The solution is to either add parentheses (if a constructor is intended) or
rename the identifier (if a fresh bound identifier is intended).

<!-- ./DafnyCore/RewritersPrecedenceLinter.cs-->

## **Warning: unusual indentation in _what_ (which starts at _location_); do you perhaps need parentheses?**

<!-- %check-resolve-warn -->
```dafny
function f(b: bool): bool
{
  b &&
  b ==> b // this parses as (b &&b) ==> b, but reads as b && (b ==> b)
}
```

Long expressions are best split up across multiple lines; readers often use indentation as a guide
to the nesting of subexpressions. For example, parallel conjuncts or disjuncts may be written with 
the same indentation. This warning occurs when the observed indentation is likely to cause
a misunderstanding of the code, particularly of the precedence of operations. It is suggested
to use parentheses or to redo the indentation to make the structure of the expression clearer.

## **Warning: unusual indentation in _what_ (which ends at _location_); do you perhaps need parentheses?**

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


<!-- ./DafnyCore/Resolver/RunAllTestsMainMethod.cs -->

## **Error: Cannot use /runAllTests on a program with a main method**

<!-- TODO - this won't be triggered until Issue 3381 is fixed -->

This error message when using `dafny test` and in the situation
where a Main method is already present in the program.  
`dafny test` synthesizes a Main method that calls all the test routines,
which then conflicts with the existing Main method.
(The `/runAllTests` option has been replaced by `dafny test`.)

## **Error: Methods with the {:test} attribute can have at most one return value**

<!-- %check-test -->
```dafny
method {:test} m(i: int) returns (j: int, k: int) 
{
  j, k := 0,0;
}
```

This error only occurs when using `dafny test`. That command executes all methods attributed
with `{:test}`, but such test methods are limited to methods with only one output parameter.
This is purely an implementation limitation.


<!-- ./DafnyCore/Resolver/ExpectContracts.cs-->

## **Warning: The _kind_ clause at this location cannot be compiled to be tested at runtime because it references ghost state.**
<!-- TODO - requires a companion target program file to run successfully -->
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
 
## **Warning: Internal: no wrapper for _name_**

This message indicates a bug within dafny. Please report the program that
triggered the message to [the Github issues site](https://www.github.com/dafny-lang/dafny/issues).

## **Warning: No :test code calls _name_**

This warning indicates that some method marked with {:extern} is not called
by any method marked with {:test}. The intention is to check coverage of
the programmed unit tests. The warning only appears when using
`/testContracts:TestedExterns` with the legacy CLI.
It is likely to be removed in a future version of dafny.

<!-- ./DafnyCore/Resolver/PrintEffectEnforcement.cs-->

## **Error: :print attribute is not allowed on functions**

<!-- %check-resolve -->
```dafny
function method {:print} f(): int { 0 }
```

The `{:print}` attribute is used to mark methods that have a side-effect of
printing something, that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
Thus Dafny forbids (ghost or compiled) functions from declaring that they have
a print side-effect (whether or not print effects are being tracked with 
`--track-print-effects`).

## **Error: :print attribute is not allowed on ghost methods**

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

## **Error: not allowed to override a non-printing method with a possibly printing method (_name_)**

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

## **Error: :print attribute does not take any arguments**

<!-- %check-resolve -->
```dafny
method {:print 42} f() { }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something.
No arguments to the attribute are needed or allowed.

## **Error: a function-by-method is not allowed to use print statements**

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


## **Error: to use a print statement, the enclosing _method_ must be marked with {:print}**

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


## **Error: a function-by-method is not allowed to call a method with print effects**

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


## **Error: to call a method with print effects, the enclosing _method_ must be marked with {:print}**

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

