
<!-- ./DafnyCore/Rewriters/TimeLimitRewriter.cs -->

## **Warning: timeLimitMultiplier annotation overrides " + name + " annotation**

<!-- TODO -->

<!-- ./DafnyCore/Rewriters/UselessOldLinter.cs -->

## **Warning: Argument to 'old' does not dereference the mutable heap, so this use of 'old' has no effect**

<!-- %check-resolve-warn Rewriter.2.expect -->
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

The `old` function, used in specifications and ghost code, indicates that the argument (an expression) is to be evaluated in some previous heap state.
So if the argument does not depend on the heap, the `old` has no effect and is likely to lead to misunderstanding.
Consequently, Dafny says that it is an error to do so.
For example, it is illegal to apply `old` to a local variable; instead one should capture
the value of the local variable in a previous state using an otherwise unused ghost variable.


<!-- ./DafnyCore/Rewriters/InductionRewriter.cs-->

## **_item_s given as :induction arguments must be given in the same order as in the _expr_; ignoring attribute**

<!-- TODO -->

## **lemma parameters given as :induction arguments must be given in the same order as in the lemma; ignoring attribute**

<!-- %check-resolve-warn Rewriter.4.expect -->
```dafny
lemma {:induction j,i} m(i: int, j: int) ensures i + j == j + i {}
```

The `{:induction}` attribute gives some guidance to the prover as to how to construct the induction argument that 
proves the lemma. Purely for convenience of implementation, the arguments of the attribute must be in the
same order as the parameters of the lemma.

## **invalid :induction attribute argument; expected _what_; ignoring attribute**

<!-- %check-resolve-warn Rewriter.5.expect -->
```dafny
lemma {:induction 42} m(i: int, j: int) ensures i + j == j + i {} 
```

The arguments of the `:induction` attribute can be any of the lemma parameters (if the declaration is for a lemma),
the `this` keyword, or true or false.

<!-- TODO , consider non-lemma case -->

<!-- ./DafnyCore/Rewriters/ConstructorWarning.cs -->

## **Constructor name '_pattern_' should be followed by parentheses**

<!-- %check-resolve-warn Rewriter.6.expect %options --warn-missing-constructor-parentheses -->
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
new variable to be bound to the match expression. If a simple identifier matches a parameter-less
constructor (if there is one of the right type) in preference to a new bound identifier.

This can lead to surprises if there is a matching constructor that the writer or the reader of the software
is unaware of. So it is useful to always write constructors with parentheses, to visually distinguish them
from simple identifiers.
The `--warn-missing-constructor-parentheses` option will warn (as in this example) if a constructor is
used without paraentheses. The solution is to either add parentheses (if a constructor is intended) or
rename the identifier (if a fresh bound identifier is intended).

<!-- ./DafnyCore/PrecedenceLinter.cs-->

## **Warning: unusual indentation in _what_ (which starts at _location_); do you perhaps need parentheses?**

<!-- TODO -->

## **Warning: unusual indentation in _what_ (which ends at _location_); do you perhaps need parentheses?**

<!-- TODO -->

<!-- ./DafnyCore/Resolver/RunAllTestsMainMethod.cs -->

## **Cannot use /runAllTests on a program with a main method**

<!-- TODO - haven't been able to trigger this error -->

The `/runAllTests` option is obsolete. Use `dafny test` instead.
This error message only occurs with the legacy interface and in the situation
where a Main method is already present in the program. With this 
option dafny synthesizes a Main method that calls all the test routines,
which then conflicts with the existing Main method.

## **Methods with the {:test} attribute can have at most one return value**

<!-- %check-test Rewriter.10.expect -->
```dafny
method {:test} m(i: int) returns (j: int, k: int) 
{
  j, k := 0,0;
}
```

This error only occurs when using `dafny test`. That command executes all methods attributed with `{:test}`,
but such test methods are limited to methods with only one output parameter.

<!-- TODO - Why? -->

<!-- ./DafnyCore/Resolver/ExpectContracts.cs-->

## **Warning: The {exprType} clause at this location cannot be compiled to be tested at runtime because it references ghost state.**

<!-- TODO -->

## **Warning: Internal: no wrapper for _name_**

<!-- TODO -->

## **Warning: No :test code calls _name_**

<!-- TODO -->

<!-- ./DafnyCore/Resolver/PrintEffectEnforcement.cs-->

## **Error: :print attribute is not allowed on functions**

<!-- %check-resolve Rewriter.14.expect -->
```dafny
function method {:print} f(): int { 0 }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
Thus Dafny forbids (ghost or compiled) functions from declaring that they have a print side-effect
(whether or not print effects are being tracked with --track-print-effects).

## **Error: :print attribute is not allowed on ghost methods**

<!-- %check-resolve Rewriter.15.expect -->
```dafny
ghost method {:print} f() { }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
A program's ghost code is not allowed to modify the actual execution of a program.
Thus ghost code should not contain print statements.
So Dafny forbids ghost methods from declaring that they have a print side-effect
(whether or not print effects are being tracked with --track-print-effects).

## **Error: not allowed to override a non-printing method with a possibly printing method (_name_)**

<!-- %check-resolve Rewriter.16.expect -->
```dafny
trait T {
  method m()
}

class C extends T {
  method {:print} m() {}
}
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
If a trait declares a method without a `{:print}` attribute, then any implementation 
of that method may not do any printing.
Thus a class implementing that method by an override cannot declare the method as possibly
printing something, by bgiving it a `{:print}` attribute --- even if it does not actually do any printing.

## **Error: :print attribute does not take any arguments**

<!-- %check-resolve Rewriter.17.expect -->
```dafny
method {:print 42} f() { }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something.
No arguments to the attribute are needed or allowed.

## **Error: a function-by-method is not allowed to use print statements**

<!-- %check-resolve Rewriter.18.expect %options --track-print-effects -->
```dafny
function f(): int {42 }
by method {
  print "I'm here\n";
  return 42;
}
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
Functions, whether ghost or compiled, are intended to have no side-effects at all.
A function-by-method has a method body that is intended to be a compiled way of computing 
what the function body expresses. But as a function may not have side-effects,
the method body should not have any print statements.

This tracking of print statements (and the forbidding of them by this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.


## **Error: to use a print statement, the enclosing _method_ must be marked with {:print}**

<!-- %check-resolve Rewriter.19.expect %options --track-print-effects -->
```dafny
method m() { print 42; }
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment. 
So a method that prints something (even transitively) should be marked with `{:print}`.
This error indicates that such an attribute is missing -- either add the attribute or remove the print statement.

This tracking of print statements (and thus the possibility of this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.


## **Error: a function-by-method is not allowed to call a method with print effects**

<!-- %check-resolve Rewriter.20.expect %options --track-print-effects -->
```dafny
function m(): int { 42 }
by method { p(); return 42; }

method {:print} p() {}
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
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

<!-- %check-resolve Rewriter.21.expect %options --track-print-effects
```dafny
method m() { p(); }

method {:print} p() {}
```

The `{:print}` attribute is used to mark methods that have a side-effect of printing something,
that is, they modify the external environment.
In this case, the method body might print something because a method that is called in the body
is attributed with `{:print}` (whether or not it actually does print something).
So the claling methd must be marked with `{:print}` as well.

This tracking of print statements (and thus the possibility of this error message)
only happens when the `--track-print-effects` option is enabled;
the option is disabled by default.


