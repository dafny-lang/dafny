# 8. Statements ([grammar](#g-statement)) {#sec-statements}

Many of Dafny's statements are similar to those in traditional
programming languages, but a number of them are significantly different.
Dafny's various kinds of statements are described in subsequent sections.

Statements have zero or more labels and end with either a semicolon (`;`) or a closing curly brace ('}').

## 8.1. Labeled Statement ([grammar](#g-labeled-statement)) {#sec-labeled-statement}

Examples:
<!-- %check-resolve -->
```dafny
class A { var f: int }
method m(a: A) {
  label x:
  while true {
     if (*) { break x; }
  }
  a.f := 0;
  label y:
  a.f := 1;
  assert old@y(a.f) == 1;
}
```

A labeled statement is just 
- the keyword `label` 
- followed by an identifier, which is the label, 
- followed by a colon 
- and a statement. 

The label may be
referenced in a `break` or `continue` statement within the labeled statement
(see [Section 8.4](#sec-break-continue-statement)). That is, the break or continue that
mentions the label must be _enclosed_ in the labeled statement.

The label may also be used in an `old` expression ([Section 9.22](#sec-old-expression)). In this case, the label
must have been encountered during the control flow en route to the `old`
expression. We say in this case that the (program point of the) label _dominates_
the (program point of the) use of the label.
Similarly, labels are used to indicate previous states in calls of [two-state predicates](#sec-two-state),
[fresh expressions](#sec-fresh-expression), [unchanged expressions](#sec-unchanged-expression), 
and [allocated expressions](#sec-allocated-expression).

A statement can be given several labels. It makes no difference which of these
labels is used to reference the statement---they are synonyms of each other.
The labels must be distinct from each other, and are not allowed to be the
same as any previous enclosing or [dominating label](#sec-two-state).

## 8.2. Block Statement ([grammar](#g-block-statement)) {#sec-block-statement}

Examples:
<!-- %no-check -->
```dafny
{
  print 0;
  var x := 0;
}
```

A block statement is a sequence of zero or more statements enclosed by curly braces.
Local variables declared in the block end their scope at the end of the block.

## 8.3. Return Statement ([grammar](#g-return-statement)) {#sec-return-statement}

Examples:
<!-- %check-resolve -->
```dafny
method m(i: int) returns (r: int) {
  return i+1;
}
method n(i: int) returns (r: int, q: int) {
  return i+1, i + 2;
}
method p() returns (i: int) {
  i := 1;
  return;
}
method q() {
  return;
}
```
  
A return statement can only be used in a method. It is used
to terminate the execution of the method.

To return a value from a method, the value is assigned to one
of the named out-parameters sometime before a return statement.
In fact, the out-parameters act very much like local variables,
and can be assigned to more than once. Return statements are
used when one wants to return before reaching the end of the
body block of the method.

Return statements can be just the `return` keyword (where the current values
of the out-parameters are used), or they can take a list of expressions to
return. If a list is given, the number of expressions given must be the same
as the number of named out-parameters. These expressions are
evaluated, then they are assigned to the out-parameters, and then the
method terminates.

## 8.4. Break and Continue Statements ([grammar](#g-break-continue-statement)) {#sec-break-continue-statement}

Examples:
<!-- %check-resolve -->
```dafny
class A { var f: int }
method m(a: A) {
  label x:
  while true {
    if (*) { break; }
  }
  label y: {
    var z := 1;
    if * { break y; }
    z := 2;
  }

}
```

Break and continue statements provide a means to transfer control
in a way different than the usual nested control structures.
There are two forms of each of these statements: with and without a label.

If a label is used, the break or continue statement must be enclosed in a statement
with that label. The enclosing statement is called the _target_ of the break
or continue.

A `break` statement transfers control to the point immediately
following the target statement. For example, such a break statement can be
used to exit a sequence of statements in a block statement before
reaching the end of the block.

For example,
<!-- %no-check -->
```dafny
label L: {
  var n := ReadNext();
  if n < 0 {
    break L;
  }
  DoSomething(n);
}
```
is equivalent to
<!-- %no-check -->
```dafny
{
  var n := ReadNext();
  if 0 <= n {
    DoSomething(n);
  }
}
```

If no label is specified and the statement lists `n`
occurrences of `break`, then the statement must be enclosed in
at least `n` levels of loop statements. Control continues after exiting `n`
enclosing loops. For example,

<!-- %check-resolve -->
```dafny
method m() {
  for i := 0 to 10 {
    for j := 0 to 10 {
      label X: {
        for k := 0 to 10 {
          if j + k == 15 {
            break break;
          }
        }
      }
    }
    // control continues here after the "break break", exiting two loops
  }
}
```

Note that a non-labeled `break` pays attention only to loops, not to labeled
statements. For example, the labeled block `X` in the previous example
does not play a role in determining the target statement of the `break break;`.

For a `continue` statement, the target statement must be a loop statement.
The continue statement transfers control to the point immediately
before the closing curly-brace of the loop body.

For example,
<!-- %check-resolve -->
```dafny
method m() {
  for i := 0 to 100 {
    if i == 17 {
      continue;
    }
    DoSomething(i);
  }
}
method DoSomething(i:int){}
```
is equivalent to
<!-- %check-resolve -->
```dafny
method m() {
  for i := 0 to 100 {
    if i != 17 {
      DoSomething(i);
    }
  }
}
method DoSomething(i:int){}
```
The same effect can also be obtained by wrapping the loop body in a labeled
block statement and then using `break` with a label, but that usually makes
for a more cluttered program:
<!-- %check-resolve -->
```dafny
method m() {
  for i := 0 to 100 {
    label LoopBody: {
      if i == 17 {
        break LoopBody;
      }
      DoSomething(i);
    }
  }
}
method DoSomething(i:int){}
```

Stated differently, `continue` has the effect of ending the current loop iteration,
after which control continues with any remaining iterations. This is most natural
for `for` loops. For a `while` loop, be careful to make progress toward termination
before a `continue` statement. For example, the following program snippet shows
an easy mistake to make (the verifier will complain that the loop may not terminate):

<!-- %check-verify Statements.1.expect -->
```dafny
method m() {
  var i := 0;
  while i < 100 {
    if i == 17 {
      continue; // error: this would cause an infinite loop
    }
    DoSomething(i);
    i := i + 1;
  }
}
method DoSomething(i:int){}
```

The `continue` statement can give a label, provided the label is a label of a loop.
For example,

<!-- %check-resolve -->
```dafny
method m() {
  label Outer:
  for i := 0 to 100 {
    for j := 0 to 100 {
      if i + j == 19 {
        continue Outer;
      }
      WorkIt(i, j);
    }
    PostProcess(i);
    // the "continue Outer" statement above transfers control to here
  }
}
method WorkIt(i:int, j:int){}
method PostProcess(i:int){}
```

If a non-labeled continue statement lists `n` occurrences of `break` before the
`continue` keyword, then the statement must be enclosed in at least `n + 1` levels
of loop statements. The effect is to `break` out of the `n` most closely enclosing
loops and then `continue` the iterations of the next loop. That is, `n` occurrences
of `break` followed by one more `break;` will break out of `n` levels of loops
and then do a `break`, whereas `n` occurrences of `break` followed by `continue;`
will break out of `n` levels of loops and then do a `continue`.

For example, the `WorkIt` example above can equivalently be written without labels
as
<!-- %check-resolve -->
```dafny
method m() {
  for i := 0 to 100 {
    for j := 0 to 100 {
      if i + j == 19 {
        break continue;
      }
      WorkIt(i, j);
    }
    PostProcess(i);
    // the "break continue" statement above transfers control to here
  }
}
method WorkIt(i:int, j:int){}
method PostProcess(i:int){}
```

Note that a loop invariant is checked on entry to a loop and at the closing curly-brace
of the loop body. It is not checked at break statements. For continue statements, 
the loop invariant is checked as usual at the closing curly-brace
that the continue statement jumps to.
This checking ensures that the loop invariant holds at the very top of
every iteration. Commonly, the only exit out of a loop happens when the loop guard evaluates
to `false`. Since no state is changed between the top of an iteration (where the loop
invariant is known to hold) and the evaluation of the loop guard, one can also rely on
the loop invariant to hold immediately following the loop. But the loop invariant may
not hold immediately following a loop if a loop iteration changes the program state and
then exits the loop with a break statement.

For example, the following program verifies:
<!-- %check-verify -->
```dafny
method m() {
  var i := 0;
  while i < 10
    invariant 0 <= i <= 10
  {
    if P(i) {
      i := i + 200;
      break;
    }
    i := i + 1;
  }
  assert i == 10 || 200 <= i < 210;
}
predicate P(i:int)
```
To explain the example, the loop invariant `0 <= i <= 10` is known to hold at the very top
of each iteration,
that is, just before the loop guard `i < 10` is evaluated. If the loop guard evaluates
to `false`, then the negated guard condition (`10 <= i`) and the invariant hold, so
`i == 10` will hold immediately after the loop. If the loop guard evaluates to `true`
(that is, `i < 10` holds), then the loop body is entered. If the test `P(i)` then evaluates
to `true`, the loop adds `200` to `i` and breaks out of the loop, so on such a
path, `200 <= i < 210` is known to hold immediately after the loop. This is summarized
in the assert statement in the example.
So, remember, a loop invariant holds at the very top of every iteration, not necessarily
immediately after the loop.

## 8.5. Yield Statement ([grammar](#g-yield-statement)) {#sec-yield-statement}

A yield statement may only be used in an iterator.
See [iterator types](#sec-iterator-types) for more details
about iterators.

The body of an iterator is a _co-routine_. It is used
to yield control to its caller, signaling that a new
set of values for the iterator's yield (out-)parameters (if any)
are available. Values are assigned to the yield parameters
at or before a yield statement.
In fact, the yield parameters act very much like local variables,
and can be assigned to more than once. Yield statements are
used when one wants to return new yield parameter values
to the caller. Yield statements can be just the
`yield` keyword (where the current values of the yield parameters
are used), or they can take a list of expressions to yield.
If a list is given, the number of expressions given must be the
same as the number of named iterator out-parameters.
These expressions are then evaluated, then they are
assigned to the yield parameters, and then the iterator
yields.

## 8.6. Update and Call Statements ([grammar](#g-update-and-call-statement)) {#sec-update-and-call-statement}

Examples:
<!-- %check-resolve -->
```dafny
class C { var f: int }
class D {
  var i: int
  constructor(i: int) {
    this.i := i;
  }
}
method q(i: int, j: int) {}
method r() returns (s: int, t: int) { return 2,3; }
method m() {
  var ss: int, tt: int, c: C?, a: array<int>, d: D?;
  q(0,1);
  ss, c.f := r();
  c := new C;
  d := new D(2);
  a := new int[10];
  ss, tt := 212, 33;
  ss :| ss > 7;
  ss := *;
}
```

This statement corresponds to familiar assignment or method call statements,
with variations. If more than one
left-hand side is used, these must denote different l-values, unless the
corresponding right-hand sides also denote the same value.

The update statement serves several logical purposes.

### 8.6.1. Method call with no out-parameters
1) Examples of method calls take this form
<!-- %no-check -->
```dafny
m();
m(1,2,3) {:attr} ;
e.f().g.m(45);
```

As there are no left-hand-side locations to receive values, this form is allowed only for 
methods that have no out-parameters.

### 8.6.2. Method call with out-parameters

This form uses `:=` to denote the assignment of the out-parameters of the method to the 
corresponding number of LHS values.
<!-- %no-check -->
```dafny
a, b.e().f := m() {:attr};
```

In this case, the right-hand-side must be a method call and the number of
left-hand sides must match the number of out-parameters of the
method that is called or there must be just one ``Lhs`` to the left of
the `:=`, which then is assigned a tuple of the out-parameters.
Note that the result of a method call is not allowed to be used as an argument of
another method call, as if it were an expression.

### 8.6.3. Parallel assignment

A parallel-assignment has one-or-more right-hand-side expressions,
which may be function calls but may not be method calls.
<!-- %no-check -->
```dafny
    x, y := y, x;
```
The above example swaps the values of `x` and `y`. If more than one
left-hand side is used, these must denote different l-values, unless the
corresponding right-hand sides also denote the same value. There must
be an equal number of left-hand sides and right-hand sides.
The most common case has only one RHS and one LHS.

### 8.6.4. Havoc assignment {#sec-havoc-statement}
The form with a right-hand-side that is `*` is a _havoc_ assignment.
It assigns an arbitrary but type-correct value to the corresponding left-hand-side.
It can be mixed with other assignments of computed values.
<!-- %no-check -->
```dafny
a := *'
a, b, c := 4, *, 5;
```

### 8.6.5. Such-that assignment

This form has one or more left-hand-sides, a `:|` symbol and then a boolean expression on the right.
The effect is to assign values to the left-hand-sides that satisfy the 
RHS condition.

<!-- %no-check -->
```dafny
x, y :| 0 < x+y < 10;
```
This is read as assign values to `x` and `y` such that `0 < x+y < 10` is true.
The given boolean expression need not constrain the LHS values uniquely:
the choice of satisfying values is non-deterministic. 
This can be used to make a choice as in the
following example where we choose an element in a set.

<!-- %check-verify -->
```dafny
method Sum(X: set<int>) returns (s: int)
{
  s := 0; var Y := X;
  while Y != {}
    decreases Y
  {
    var y: int;
    y :| y in Y;
    s, Y := s + y, Y - {y};
  }
}
```

Dafny will report an error if it cannot prove that values
exist that satisfy the condition. 

In this variation, with an `assume` keyword
<!-- %no-check -->
```dafny
    y :| assume y in Y;
```
Dafny assumes without proof that an appropriate value exists.


Note that the syntax

```text
    Lhs ":"
```

is interpreted as a label in which the user forgot the `label` keyword.

## 8.7. Update with Failure Statement (`:-`) ([grammar](#g-update-with-failure-statement)) {#sec-update-with-failure-statement}

See the subsections below for examples.

A `:-`[^elephant] statement is an alternate form of the `:=` statement that allows for abrupt return if a failure is detected.
This is a language feature somewhat analogous to exceptions in other languages.

[^elephant]: The `:-` token is called the elephant symbol or operator.

An update-with-failure statement uses _failure-compatible_ types.
A failure-compatible type is a type that has the following (non-static) members (each with no in-parameters and one out-parameter):

 * a non-ghost function `IsFailure()` that returns a `bool`
 * an optional non-ghost function `PropagateFailure()` that returns a value assignable to the first out-parameter of the caller
 * an optional function `Extract()`
(PropagateFailure and Extract were permitted to be methods (but deprecated) prior to Dafny 4. They will be required to be functions in Dafny 4.)

A failure-compatible type with an `Extract` member is called _value-carrying_.

To use this form of update,

 * if the RHS of the update-with-failure statement is a method call, the first out-parameter of the callee must be failure-compatible
 * if instead, the RHS of the update-with-failure statement is one or more expressions, the first of these expressions must be a value with a failure-compatible type
 * the caller must have a first out-parameter whose type matches the output of `PropagateFailure` applied to the first output of the callee, unless an
`expect`, `assume`, or `assert` keyword is used after `:-` (cf. [Section 8.7.7](#sec-failure-return-keyword)).
 * if the failure-compatible type of the RHS does not have an `Extract` member,
then the LHS of the `:-` statement has one less expression than the RHS
(or than the number of out-parameters from the method call), the value of the first out-parameter or expression being dropped
(see the discussion and examples in [Section 8.7.2](#sec-simple-fc-return))
 * if the failure-compatible type of the RHS does have an `Extract` member,
then the LHS of the `:-` statement has the same number of expressions as the RHS
(or as the number of out-parameters from the method call)
and the type of the first LHS expression must be assignable from the return type of the `Extract` member
* the `IsFailure` and `PropagateFailure` methods may not be ghost
* the LHS expression assigned the output of the `Extract` member is ghost precisely if `Extract` is ghost

The following subsections show various uses and alternatives.

### 8.7.1. Failure compatible types {#sec-failure-compatible-types}

A simple failure-compatible type is the following:
<!-- %check-resolve -->
```dafny
datatype Status =
| Success
| Failure(error: string)
{
  predicate IsFailure() { this.Failure?  }
  function PropagateFailure(): Status
    requires IsFailure()
  {
    Failure(this.error)
  }
}
``` <!-- %save Status.tmp -->

A commonly used alternative that carries some value information is something like this generic type:
<!-- %check-resolve -->
```dafny
datatype Outcome<T> =
| Success(value: T)
| Failure(error: string)
{
  predicate IsFailure() {
    this.Failure?
  }
  function PropagateFailure<U>(): Outcome<U>
    requires IsFailure()
  {
    Failure(this.error) // this is Outcome<U>.Failure(...)
  }
  function Extract(): T
    requires !IsFailure()
  {
    this.value
  }
}
``` <!-- %save Outcome.tmp -->


### 8.7.2. Simple status return with no other outputs {#sec-simple-fc-return}

The simplest use of this failure-return style of programming is to have a method call that just returns a non-value-carrying `Status` value:
<!-- %check-resolve %use Status.tmp -->
```dafny
method Callee(i: int) returns (r: Status)
{
  if i < 0 { return Failure("negative"); }
  return Success;
}

method Caller(i: int) returns (rr: Status)
{
  :- Callee(i);
  ...
}
```

Note that there is no LHS to the `:-` statement.
If `Callee` returns `Failure`, then the caller immediately returns,
not executing any statements following the call of `Callee`.
The value returned by `Caller` (the value of `rr` in the code above) is the result of `PropagateFailure` applied to the value returned by `Callee`, which is often just the same value.
If `Callee` does not return `Failure` (that is, returns a value for which `IsFailure()` is `false`)
then that return value is forgotten and execution proceeds normally with the statements following the call of `Callee` in the body of `Caller`.

The desugaring of the `:- Callee(i);` statement is
<!-- %no-check -->
```dafny
var tmp;
tmp := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
In this and subsequent examples of desugaring, the `tmp` variable is a new, unique variable, unused elsewhere in the calling member.

### 8.7.3. Status return with additional outputs {#sec-multiple-output-fc}

The example in the previous subsection affects the program only through side effects or the status return itself.
It may well be convenient to have additional out-parameters, as is allowed for `:=` updates;
these out-parameters behave just as for `:=`.
Here is an example:

<!-- %check-resolve %use Status.tmp -->
```dafny
method Callee(i: int) returns (r: Status, v: int, w: int)
{
  if i < 0 { return Failure("negative"), 0, 0; }
  return Success, i+i, i*i;
}

method Caller(i: int) returns (rr: Status, k: int)
{
  var j: int;
  j, k :- Callee(i);
  k := k + k;
  ...
}
```

Here `Callee` has two outputs in addition to the `Status` output.
The LHS of the `:-` statement accordingly has two l-values to receive those outputs.
The recipients of those outputs may be any sort of l-values;
here they are a local variable and an out-parameter of the caller.
Those outputs are assigned in the `:-` call regardless of the `Status` value:

   * If `Callee` returns a failure value as its first output, then the other outputs are assigned, 
the _caller's_ first out-parameter (here `rr`) is assigned the value of `PropagateFailure`, and the caller returns.
   * If `Callee` returns a non-failure value as its first output, then the other outputs are assigned and the
caller continues execution as normal.

The desugaring of the `j, k :- Callee(i);` statement is
<!-- %no-check -->
```dafny
var tmp;
tmp, j, k := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```


### 8.7.4. Failure-returns with additional data {#sec-value-carrying}

The failure-compatible return value can carry additional data as shown in the `Outcome<T>` example above.
In this case there is a (first) LHS l-value to receive this additional data. The type of that first LHS
value is one that is assignable from the result of the `Extract` function, not the actual first out-parameter.

<!-- %check-resolve %use Outcome.tmp -->
```dafny
method Callee(i: int) returns (r: Outcome<nat>, v: int)
{
  if i < 0 { return Failure("negative"), i+i; }
  return Success(i), i+i;
}

method Caller(i: int) returns (rr: Outcome<int>, k: int)
{
  var j: int;
  j, k :- Callee(i);
  k := k + k;
  ...
}
```

Suppose `Caller` is called with an argument of `10`.
Then `Callee` is called with argument `10`
and returns `r` and `v` of `Outcome<nat>.Success(10)` and `20`.
Here `r.IsFailure()` is `false`, so control proceeds normally.
The `j` is assigned the result of `r.Extract()`, which will be `10`,
and `k` is assigned `20`.
Control flow proceeds to the next line, where `k` now gets the value `40`.

Suppose instead that `Caller` is called with an argument of `-1`.
Then `Callee` is called with the value `-1`
 and returns `r` and `v` with values `Outcome<nat>.Failure("negative")` and `-2`.
`k` is assigned the value of `v` (-2).
But `r.IsFailure()` is `true`, so control proceeds directly to return from `Caller`.
The first out-parameter of `Caller` (`rr`) gets the value of `r.PropagateFailure()`,
which is `Outcome<int>.Failure("negative")`; `k` already has the value `-2`.
The rest of the body of `Caller` is skipped.
In this example, the first out-parameter of `Caller` has a failure-compatible type
so the exceptional return will propagate up the call stack.
It will keep propagating up the call stack
as long as there are callers with this first special output type
and calls that use `:-`
and the return value keeps having `IsFailure()` true.

The desugaring of the `j, k :- Callee(i);` statement in this example is
<!-- %no-check -->
```dafny
var tmp;
tmp, k := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
j := tmp.Extract();
```

### 8.7.5. RHS with expression list {#sec-failure-expressions}

Instead of a failure-returning method call on the RHS of the statement,
the RHS can instead be a list of expressions.
As for a `:=` statement, in this form, the expressions on the left and right sides of `:-` must correspond,
just omitting a LHS l-value for the first RHS expression if its type is not value-carrying.
The semantics is very similar to that in the previous subsection.

 * The first RHS expression must have a failure-compatible type.
 * All the assignments of RHS expressions to LHS values except for the first RHS value are made.
 * If the first RHS value (say `r`) responds `true` to `r.IsFailure()`,
then `r.PropagateFailure()` is assigned to the first out-parameter of the _caller_
and the execution of the caller's body is ended.
 * If the first RHS value (say `r`) responds `false` to `r.IsFailure()`, then
   * if the type of `r` is value-carrying, then `r.Extract()` is assigned to the first LHS value of the `:-` statement;
if `r` is not value-carrying, then the corresponding LHS l-value is omitted
   * execution of the caller's body continues with the statement following the `:-` statement.

A RHS with a method call cannot be mixed with a RHS containing multiple expressions.

For example, the desugaring of
<!-- %check-resolve %use Status.tmp -->
```dafny
method m(r: Status) returns (rr: Status) {
  var k;
  k :- r, 7;
  ...
}
```
is
<!-- %no-check -->
```dafny
var k;
var tmp;
tmp, k := r, 7;
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
### 8.7.6. Failure with initialized declaration. {#sec-failure-with-declaration}

The `:-` syntax can also be used in initialization, as in
<!-- %no-check -->
```dafny
var s, t :- M();
```
This is equivalent to
<!-- %no-check -->
```dafny
var s, t;
s, t :- M();
```
with the semantics as described above.

### 8.7.7. Keyword alternative {#sec-failure-return-keyword}

In any of the above described uses of `:-`, the `:-` token may be followed immediately by the keyword `expect`, `assert` or `assume`.

* `assert` means that the RHS evaluation is expected to be successful, but that
the verifier should prove that this is so; that is, the verifier should prove
`assert !r.IsFailure()` (where `r` is the status return from the callee)
(cf. [Section 8.16](#sec-assert-statement))
* `assume` means that the RHS evaluation should be assumed to be successful,
as if the statement `assume !r.IsFailure()` followed the evaluation of the RHS
(cf. [Section 8.17](#sec-assume-statement))
* `expect` means that the RHS evaluation should be assumed to be successful
(like using `assume` above), but that the compiler should include a
run-time check for success. This is equivalent to including
`expect !r.IsFailure()` after the RHS evaluation; that is, if the status
return is a failure, the program halts.
(cf. [Section 8.18](#sec-expect-statement))

In each of these cases, there is no abrupt return from the caller. Thus
there is no evaluation of `PropagateFailure`. Consequently the first
out-parameter of the caller need not match the return type of
`PropagateFailure`; indeed, the failure-compatible type returned by the
callee need not have a `PropagateFailure` member.

The equivalent desugaring replaces
<!-- %no-check -->
```dafny
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
with
<!-- %no-check -->
```dafny
expect !tmp.IsFailure(), tmp;
```
or
<!-- %no-check -->
```dafny
assert !tmp.IsFailure();
```
or
<!-- %no-check -->
```dafny
assume !tmp.IsFailure();
```

There is a grammatical nuance that the user should be aware of.
The keywords `assert`, `assume`, and `expect` can start an expression.
For example, `assert P; E` can be an expression. However, in
`e :- assert P; E;` the `assert` is parsed as the keyword associated with
`:-`. To have the `assert` considered part of the expression use parentheses:
`e :- (assert P; E);`.

### 8.7.8. Key points

There are several points to note.

* The first out-parameter of the callee is special.
  It has a special type and that type indicates that the value is inspected to see if an abrupt return
  from the caller is warranted.
  This type is often a datatype, as shown in the examples above, but it may be any type with the appropriate members.
* The restriction on the type of caller's first out-parameter is
  just that it must be possible (perhaps through generic instantiation and type inference, as in these examples) 
  for `PropagateFailure` applied to the failure-compatible output from the callee to produce a value of 
  the caller's first out-parameter type.
  If the caller's first out-parameter type is failure-compatible (which it need not be),
  then failures can be propagated up the call chain.
  If the keyword form (e.g. `assume`) of the statement is used, then no `PropagateFailure` member
  is needed, because no failure can occur, and there is no restriction on the caller's first out-parameter.
* In the statement `j, k :- Callee(i);`,
  when the callee's return value has an `Extract` member,
  the type of `j` is not the type of the first out-parameter of `Callee`.
  Rather it is a type assignable from the output type of `Extract` applied to the first out-value of `Callee`.
* A method like `Callee` with a special first out-parameter type can still be used in the normal way:
  `r, k := Callee(i)`.
  Now `r` gets the first output value from `Callee`, of type `Status` or `Outcome<nat>` in the examples above.
  No special semantics or exceptional control paths apply.
  Subsequent code can do its own testing of the value of `r`
  and whatever other computations or control flow are desired.
* The caller and callee can have any (positive) number of output arguments,
  as long as the callee's first out-parameter has a failure-compatible type
  and the caller's first out-parameter type matches `PropagateFailure`.
* If there is more than one LHS, the LHSs must denote different l-values, 
  unless the RHS is a list of expressions and the corresponding RHS values are equal.
* The LHS l-values are evaluated before the RHS method call,
  in case the method call has side-effects or return values that modify the l-values prior to assignments being made.

It is important to note the connection between the failure-compatible types used in the caller and callee,
if they both use them.
They do not have to be the same type, but they must be closely related,
as it must be possible for the callee's `PropagateFailure` to return a value of the caller's failure-compatible type.
In practice this means that one such failure-compatible type should be used for an entire program.
If a Dafny program uses a library shared by multiple programs, the library should supply such a type 
and it should be used by all the client programs (and, effectively, all Dafny libraries).
It is also the case that it is inconvenient to mix types such as `Outcome` and `Status` above within the same program.
If there is a mix of failure-compatible types, then the program will need to use `:=` statements and code for
explicit handling of failure values.


### 8.7.9. Failure returns and exceptions

The `:-` mechanism is like the exceptions used in other programming languages, with some similarities and differences.

 * There is essentially just one kind of 'exception' in Dafny,
the variations of the failure-compatible data type.
 * Exceptions are passed up the call stack whether or not intervening methods are aware of the possibility of an exception,
that is, whether or not the intervening methods have declared that they throw exceptions.
Not so in Dafny: a failure is passed up the call stack only if each caller has a failure-compatible first out-parameter, is itself called in a `:-` statement, and returns a value that responds true to `IsFailure()`.
 * All methods that contain failure-return callees must explicitly handle those failures
using either `:-` statements or using `:=` statements with a LHS to receive the failure value.

## 8.8. Variable Declaration Statement ([grammar](#g-variable-declaration-statement)) {#sec-variable-declaration-statement}

Examples:
<!-- %check-resolve -->
```dafny
method m() {
  var x, y: int; // x's type is inferred, not necessarily 'int'
  var b: bool, k: int;
  x := 1; // settles x's type
}
```

A variable declaration statement is used to declare one or more local variables in
a method or function. The type of each local variable must be given
unless its type can be inferred, either from a given initial value, or
from other uses of the variable. If initial values are given, the number
of values must match the number of variables declared.

The scope of the declared variable extends to the end of the block in which it is
declared. However, be aware that if a simple variable declaration is followed
by an expression (rather than a subsequent statement) then the `var` begins a
[Let Expression](#sec-let-expression) and the scope of the introduced variables is
only to the end of the expression. In this case, though, the `var` is in an expression
context, not a statement context.

Note that the type of each variable must be given individually. The following code

<!-- %no-check -->
```dafny
var x, y : int;
var x, y := 5, 6;
var x, y :- m();
var x, y :| 0 < x + y < 10;
var (x, y) := makePair();
var Cons(x, y) = ConsMaker();
```
does not declare both `x` and `y` to be of type `int`. Rather it will give an
error explaining that the type of `x` is underspecified if it cannot be
inferred from uses of x.

The variables can be initialized with syntax similar to update statements (cf. [Section 8.6](#sec-update-and-call-statement)).

If the RHS is a call, then any variable receiving the value of a
formal ghost out-parameter will automatically be declared as ghost, even
if the `ghost` keyword is not part of the variable declaration statement.

The left-hand side can also contain a tuple of patterns that will be
matched against the right-hand-side. For example:

<!-- %check-resolve -->
```dafny
function returnsTuple() : (int, int)
{
    (5, 10)
}

function usesTuple() : int
{
    var (x, y) := returnsTuple();
    x + y
}
```

The initialization with failure operator `:-` returns from the enclosing method if the initializer evaluates to a failure value of a failure-compatible type (see [Section 8.7](#sec-update-with-failure-statement)).

## 8.9. Guards ([grammar](#g-guard)) {#sec-guard}

Examples (in `if` statements):
<!-- %check-resolve -->
```dafny
method m(i: int) {
  if (*) { print i; }
  if i > 0 { print i; }
}
```

Guards are used in `if` and `while` statements as boolean expressions. Guards
take two forms.

The first and most common form is just a boolean expression.

The second form is either `*` or `(*)`. These have the same meaning. An
unspecified boolean value is returned. The value returned
may be different each time it is executed.

## 8.10. Binding Guards ([grammar](#g-binding-guard)) {#sec-binding-guards}

Examples (in `if` statements):
<!-- %check-resolve-warn Statements.13.expect -->
```dafny
method m(i: int) {
  ghost var k: int;
  if i, j :| 0 < i+j < 10 {
    k := 0;
  } else {
    k := 1;
  }
}
```

An `if` statement can also take a _binding guard_.
Such a guard checks if there exist values for the given variables that satisfy the given expression.
If so, it binds some satisfying values to the variables and proceeds
into the "then" branch; otherwise it proceeds with the "else" branch,
where the bound variables are not in scope.

In other words, the statement

<!-- %no-check -->
```dafny
if x :| P { S } else { T }
```

has the same meaning as

<!-- %no-check -->
```dafny
if exists x :: P { var x :| P; S } else { T }
```

The identifiers bound by the binding guard are ghost variables
and cannot be assigned to non-ghost variables. They are only
used in specification contexts.

Here is another example:

<!-- %check-verify -->
```dafny
predicate P(n: int)
{
  n % 2 == 0
}

method M1() returns (ghost y: int)
    requires exists x :: P(x)
    ensures P(y)
{
  if x : int :| P(x) {
      y := x;
  }
}
```

## 8.11. If Statement ([grammar](#g-if-statement)) {#sec-if-statement}

Examples:
<!-- %check-resolve-warn Statements.14.expect -->
```dafny
method m(i: int) {
  var x: int;
  if i > 0 {
    x := i;
  } else {
    x := -i;
  }
  if * {
    x := i;
  } else {
    x := -i;
  }
  if i: nat, j: nat :| i+j<10 {
    assert i < 10;
  }
  if i == 0 {
    x := 0;
  } else if i > 0 {
    x := 1;
  } else {
    x := -1;
  }
  if 
    case i == 0 => x := 0;
    case i > 0 => x := 1;
    case i < 0 => x := -1;
}
```

The simplest form of an `if` statement uses a guard that is a boolean
expression. For example,

<!-- %no-check -->
```dafny
  if x < 0 {
    x := -x;
  }
```

Unlike `match` statements, `if` statements do not have to be exhaustive:
omitting the `else` block is the same as including an empty `else`
block.  To ensure that an `if` statement is exhaustive, use the
`if-case` statement documented below.

If the guard is an asterisk then a non-deterministic choice is made:

<!-- %no-check -->
```dafny
  if * {
    print "True";
  } else {
    print "False";
  }
```

The then alternative of the if-statement must be a block statement;
the else alternative may be either a block statement or another if statement.
The condition of the if statement need not (but may) be enclosed in parentheses.

An if statement with a binding guard is non-deterministic;
it will not be compiled if `--enforce-determinism` is enabled
(even if it can be proved that there is a unique value).
An if statement with `*` for a guard is non-deterministic and ghost.

The `if-case` statement using the `AlternativeBlock` form is similar to the
`if ... fi` construct used in the book "A Discipline of Programming" by
Edsger W. Dijkstra. It is used for a multi-branch `if`.

For example:
<!-- %check-resolve -->
```dafny
method m(x: int, y: int) returns (max: int) 
{
  if {
    case x <= y => max := y;
    case y <= x => max := x;
  }
}
```

In this form, the expressions following the `case` keyword are called
_guards_. The statement is evaluated by evaluating the guards in an
undetermined order until one is found that is `true` and the statements
to the right of `=>` for that guard are executed. The statement requires
at least one of the guards to evaluate to `true` (that is, `if-case`
statements must be exhaustive: the guards must cover all cases).

In the if-with-cases, a sequence of statements may follow the `=>`; it
may but need not be a block statement (a brace-enclosed sequence of statements).

The form that used `...` (a refinement feature) as the guard is deprecated.

## 8.12. While Statement ([grammar](#g-while-statement)) {#sec-while-statement}

Examples:
<!-- %check-resolve -->
```dafny
method m() {
  var i := 10;
  while 0 < i
    invariant 0 <= i <= 10;
    decreases i;
  {
    i := i-1;
  }
  while * {}
  i := *;
  while 
     decreases if i < 0 then -i else i
  {
     case i < 0 => i := i + 1;
     case i > 0 => i := i - 1;
  }
}
```

Loops
- may be a conventional loop with a condition and a block statement for a body
- need not have parentheses around the condition
- may have a `*` for the condition (the loop is then non-deterministic)
- binding guards are not allowed
- may have a case-based structure
- may have no body --- a bodyless loop is not compilable, but can be reaosnaed about

Importantly, loops need _loop specifications_ in order for Dafny to prove that
they obey expected behavior. In some cases Dafny can infer the loop specifications by analyzing the code,
so the loop specifications need not always be explicit.
These specifications are described in [Section 7.6](#sec-loop-specification) and [Section 8.14](#sec-loop-specifications).

The general loop statement in Dafny is the familiar `while` statement.
It has two general forms.

The first form is similar to a while loop in a C-like language. For
example:

<!-- %check-resolve -->
```dafny
method m(){
  var i := 0;
  while i < 5 {
    i := i + 1;
  }
}
```

In this form, the condition following the `while` is one of these:

* A boolean expression. If true it means execute one more
iteration of the loop. If false then terminate the loop.
* An asterisk (`*`), meaning non-deterministically yield either
`true` or `false` as the value of the condition

The _body_ of the loop is usually a block statement, but it can also
be missing altogether.
A loop with a missing body may still pass verification, but any attempt
to compile the containing program will result in an error message.
When verifying a loop with a missing body, the verifier will skip attempts
to prove loop invariants and decreases assertions that would normally be
asserted at the end of the loop body.
There is more discussion about bodyless loops in [Section 8.14.4](#sec-bodyless-constructs).

The second form uses a case-based block. It is similar to the
`do ... od` construct used in the book "A Discipline of Programming" by
Edsger W. Dijkstra. For example:

<!-- %check-verify -->
```dafny
method m(n: int){
  var r := n;
  while
    decreases if 0 <= r then r else -r;
  {
    case r < 0 =>
      r := r + 1;
    case 0 < r =>
      r := r - 1;
  }
}
```
For this form, the guards are evaluated in some undetermined order
until one is found that is true, in which case the corresponding statements
are executed and the while statement is repeated.
If none of the guards evaluates to true, then the
loop execution is terminated.

The form that used `...` (a refinement feature) as the guard is deprecated.

## 8.13. For Loops ([grammar](#g-for-statement)) {#sec-for-statement}

Examples:
<!-- %check-resolve-warn Statements.15.expect -->
```dafny
method m() decreases * {
  for i := 0 to 10 {}
  for _ := 0 to 10 {}
  for i := 0 to * invariant i >= 0 decreases * {}
  for i: int := 10 downto 0 {}
  for i: int := 10 downto 0 
}
```
The `for` statement provides a convenient way to write some common loops.

The statement introduces a local variable with optional type, which is called
the _loop index_. The loop index is in scope in the specification and the body,
but not after the `for` loop. Assignments to the loop index are not allowed.
The type of the loop index can typically be inferred; if so, it need not be given
explicitly. If the identifier is not used, it can be written as `_`, as illustrated
in this repeat-20-times loop:
<!-- %no-check -->
```dafny
for _ := 0 to 20 {
  Body
}
```

There are four basic variations of the `for` loop:
<!-- %no-check -->
```dafny
for i: T := lo to hi
  LoopSpec
{ Body }

for i: T := hi downto lo
  LoopSpec
{ Body }

for i: T := lo to *
  LoopSpec
{ Body }

for i: T := hi downto *
  LoopSpec
{ Body }
```
Semantically, they are defined as the following respective `while` loops:
<!-- %no-check -->
```dafny
{
  var _lo, _hi := lo, hi;
  assert _lo <= _hi && forall _i: int :: _lo <= _i <= _hi ==> _i is T;
  var i := _lo;
  while i != _hi
    invariant _lo <= i <= _hi
    LoopSpec
    decreases _hi - i
  {
    Body
    i := i + 1;
  }
}

{
  var _lo, _hi := lo, hi;
  assert _lo <= _hi && forall _i: int :: _lo <= _i <= _hi ==> _i is T;
  var i := _hi;
  while i != lo
    invariant _lo <= i <= _hi
    LoopSpec
    decreases i - _lo
  {
    i := i - 1;
    Body
  }
}

{
  var _lo := lo;
  assert forall _i: int :: _lo <= _i ==> _i is T;
  var i := _lo;
  while true
    invariant _lo <= i
    LoopSpec
  {
    Body
    i := i + 1;
  }
}

{
  var _hi := hi;
  assert forall _i: int :: _i <= _hi ==> _i is T;
  var i := _hi;
  while true
    invariant i <= _hi
    LoopSpec
  {
    i := i - 1;
    Body
  }
}
```

The expressions `lo` and `hi` are evaluated just once, before the loop
iterations start.

Also, in all variations the values of `i` in the body are the values
from `lo` to, _but not including_, `hi`. This makes it convenient to
write common loops, including these:

<!-- %no-check -->
```dafny
for i := 0 to a.Length {
  Process(a[i]);
}
for i := a.Length downto 0 {
  Process(a[i]);
}
```
Nevertheless, `hi` must be a legal value for the type of the index variable,
since that is how the index variable is used in the invariant.

If the end-expression is not `*`, then no explicit `decreases` is
allowed, since such a loop is already known to terminate.
If the end-expression is `*`, then the absence of an explicit `decreases`
clause makes it default to `decreases *`. So, if the end-expression is `*` and no
explicit `decreases` clause is given, the loop is allowed only in methods
that are declared with `decreases *`.

The directions `to` or `downto` are contextual keywords. That is, these two
words are part of the syntax of the `for` loop, but they are not reserved
keywords elsewhere.

Just like for while loops, the body of a for-loop may be omitted during
verification. This suppresses attempts to check assertions (like invariants)
that would occur at the end of the loop. Eventually, however a body must
be provided; the compiler will not compile a method containing a body-less
for-loop. There is more discussion about bodyless loops in [Section 8.14.4](#sec-bodyless-constructs).


## 8.14. Loop Specifications {#sec-loop-specifications}
For some simple loops, such as those mentioned previously, Dafny can figure
out what the loop is doing without more help. However, in general the user
must provide more information in order to help Dafny prove the effect of
the loop. This information is provided by a _loop specification_. A
loop specification provides information about invariants, termination, and
what the loop modifies.
For additional tutorial information see [@KoenigLeino:MOD2011] or the
[online Dafny tutorial](../OnlineTutorial/guide).

### 8.14.1. Loop invariants {#sec-loop-invariants}

Loops present a problem for specification-based reasoning. There is no way to
know in advance how many times the code will go around the loop and
a tool cannot reason about every one of a possibly unbounded sequence of unrollings.
In order to consider all paths through a program, specification-based
program verification tools require loop invariants, which are another kind of
annotation.

A loop invariant is an expression that holds just prior to the loop test,
that is, upon entering a loop and
after every execution of the loop body. It captures something that is
invariant, i.e. does not change, about every step of the loop. Now,
obviously we are going to want to change variables, etc. each time around
the loop, or we wouldn't need the loop. Like pre- and postconditions, an
invariant is a property that is preserved for each execution of the loop,
expressed using the same boolean expressions we have seen. For example,

<!-- %no-check -->
```dafny
var i := 0;
while i < n
  invariant 0 <= i
{
  i := i + 1;
}
```

When you specify an invariant, Dafny proves two things: the invariant
holds upon entering the loop, and it is preserved by the loop. By
preserved, we mean that assuming that the invariant holds at the
beginning of the loop (just prior to the loop test), we must show that executing the loop body once
makes the invariant hold again. Dafny can only know upon analyzing the
loop body what the invariants say, in addition to the loop guard (the
loop condition). Just as Dafny will not discover properties of a method
on its own, it will not know that any but the most basic properties of a loop
are preserved unless it is told via an invariant.

### 8.14.2. Loop termination {#sec-loop-termination}

Dafny proves that code terminates, i.e. does not loop forever, by using
`decreases` annotations. For many things, Dafny is able to guess the right
annotations, but sometimes it needs to be made explicit.
There are two places Dafny proves termination: loops and recursion.
Both of these situations require either an explicit annotation or a
correct guess by Dafny.

A `decreases` annotation, as its name suggests, gives Dafny an expression
that decreases with every loop iteration or recursive call. There are two
conditions that Dafny needs to verify when using a `decreases` expression:

* that the expression actually gets smaller, and
* that it is bounded.

That is, the expression must strictly decrease in a well-founded ordering
(cf. [Section 12.7](#sec-well-founded-orders)).

Many times, an integral value (natural or plain integer) is the quantity
that decreases, but other values can be used as well. In the case of
integers, the bound is assumed to be zero.
For each loop iteration the `decreases` expression at the end of the loop
body must be strictly smaller than its value at the beginning of the loop
body (after the loop test). For integers, the well-founded relation between
`x` and `X` is `x < X && 0 <= X`.
Thus if the `decreases` value (`X`) is negative at the
loop test, it must exit the loop, since there is no permitted value for
`x` to have at the end of the loop body.

For example, the following is
a proper use of `decreases` on a loop:

<!-- %check-verify -->
```dafny
method m(n: nat){
  var i := n;
  while 0 < i
    invariant 0 <= i
    decreases i
  {
    i := i - 1;
  }
}
```

Here Dafny has all the ingredients it needs to prove termination. The
variable `i` becomes smaller each loop iteration, and is bounded below by
zero. When `i` becomes 0, the lower bound of the well-founded order, control
flow exits the loop.

This is fine, except the loop is backwards from most loops, which
tend to count up instead of down. In this case, what decreases is not the
counter itself, but rather the distance between the counter and the upper
bound. A simple trick for dealing with this situation is given below:

<!-- %check-verify -->
```dafny
method m(m: nat, n: int) {
  assume m <= n;
  var i := m;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}
```

This is actually Dafny's guess for this situation, as it sees `i < n` and
assumes that `n - i` is the quantity that decreases. The upper bound of the
loop invariant implies that `0 <= n – i`, and gives Dafny a lower bound on
the quantity. This also works when the bound `n` is not constant, such as
in the binary search algorithm, where two quantities approach each other,
and neither is fixed.

If the `decreases` clause of a loop specifies `*`, then no
termination check will be performed. Use of this feature is sound only with
respect to partial correctness.

### 8.14.3. Loop framing {#sec-loop-framing}

The specification of a loop also includes _framing_, which says what the
loop modifies. The loop frame includes both local variables and locations
in the heap.

For local variables, the Dafny verifier performs a syntactic
scan of the loop body to find every local variable or out-parameter that occurs as a left-hand
side of an assignment. These variables are called
_syntactic assignment targets of the loop_, or _syntactic loop targets_ for short.
Any local variable or out-parameter that is not a syntactic assignment target is known by the
verifier to remain unchanged by the loop.

The heap may or may not be a syntactic loop target. It is when the loop body
syntactically contains a statement that can modify a heap location. This
includes calls to compiled methods, even if such a method has an empty
`modifies` clause, since a compiled method is always allowed to allocate
new objects and change their values in the heap.

If the heap is not a syntactic loop target, then the verifier knows the heap
remains unchanged by the loop. If the heap _is_ a syntactic loop target,
then the loop's effective `modifies` clause determines what is allowed to be
modified by iterations of the loop body.

A loop can use `modifies` clauses to declare the effective `modifies` clause
of the loop. If a loop does not explicitly declare any `modifies` clause, then
the effective `modifies` clause of the loop is the effective `modifies` clause
of the most tightly enclosing loop or, if there is no enclosing loop, the
`modifies` clause of the enclosing method.

In most cases, there is no need to give an explicit `modifies` clause for a
loop. The one case where it is sometimes needed is if a loop modifies less
than is allowed by the enclosing method. Here are two simple methods that
illustrate this case:

<!-- %check-verify Statements.2.expect -->
```dafny
class Cell {
  var data: int
}

method M0(c: Cell, d: Cell)
  requires c != d
  modifies c, d
  ensures c.data == d.data == 100
{
  c.data, d.data := 100, 0;
  var i := 0;
  while i < 100
    invariant d.data == i
    // Needs "invariant c.data == 100" or "modifies d" to verify
  {
    d.data := d.data + 1;
    i := i + 1;
  }
}

method M1(c: Cell)
  modifies c
  ensures c.data == 100
{
  c.data := 100;
  var i := 0;
  while i < 100
    // Needs "invariant c.data == 100" or "modifies {}" to verify
  {
    var tmp := new Cell;
    tmp.data := i;
    i := i + 1;
  }
}
```

In `M0`, the effective `modifies` clause of the loop is `modifies c, d`. Therefore,
the method's postcondition `c.data == 100` is not provable. To remedy the situation,
the loop needs to be declared either with `invariant c.data == 100` or with
`modifies d`.

Similarly, the effective `modifies` clause of the loop in `M1` is `modifies c`. Therefore,
the method's postcondition `c.data == 100` is not provable. To remedy the situation,
the loop needs to be declared either with `invariant c.data == 100` or with
`modifies {}`.

When a loop has an explicit `modifies` clause, there is, at the top of
every iteration, a proof obligation that

* the expressions given in the `modifies` clause are well-formed, and
* everything indicated in the loop `modifies` clause is allowed to be modified by the
  (effective `modifies` clause of the) enclosing loop or method.

### 8.14.4. Body-less methods, functions, loops, and aggregate statements {#sec-bodyless-constructs}

Methods (including lemmas), functions, loops, and `forall` statements are ordinarily
declared with a body, that is, a curly-braces pair that contains (for methods, loops, and `forall`)
a list of zero-or-more statements or (for a function) an expression. In each case, Dafny syntactically
allows these constructs to be given without a body (no braces at all). This is to allow programmers to
temporarily postpone the development of the implementation of the method, function, loop, or
aggregate statement.

If a method has no body, there is no difference for callers of the method. Callers still reason
about the call in terms of the method's specification. But without a body, the verifier has
no method implementation to check against the specification, so the verifier is silently happy.
The compiler, on the other hand, will complain if it encounters a body-less method, because the
compiler is supposed to generate code for the method, but it isn't clever enough to do that by
itself without a given method body. If the method implementation is provided by code written
outside of Dafny, the method can be marked with an `{:extern}` annotation, in which case the
compiler will no longer complain about the absence of a method body; the verifier will not 
object either, even though there is now no proof that the Dafny specifications are satisfied
by the external implementation.

A lemma is a special kind of (ghost) method. Callers are therefore unaffected by the absence of a body,
and the verifier is silently happy with not having a proof to check against the lemma specification.
Despite a lemma being ghost, it is still the compiler that checks for, and complains about,
body-less lemmas. A body-less lemma is an unproven lemma, which is often known as an _axiom_.
If you intend to use a lemma as an axiom, omit its body and add the attribute `{:axiom}`, which
causes the compiler to suppress its complaint about the lack of a body.

Similarly, calls to a body-less function use only the specification of the function. The
verifier is silently happy, but the compiler complains (whether or not the function is ghost).
As for methods and lemmas, the `{:extern}` and `{:axiom}` attributes can be used to suppress the
compiler's complaint.

By supplying a body for a method or function, the verifier will in effect show the feasibility of
the specification of the method or function. By supplying an `{:extern}` or `{:axiom}` attribute,
you are taking that responsibility into your own hands. Common mistakes include forgetting to
provide an appropriate `modifies` or `reads` clause in the specification, or forgetting that
the results of functions in Dafny (unlike in most other languages) must be deterministic.

Just like methods and functions have two sides, callers and implementations, loops also have
two sides. One side (analogous to callers) is the context that uses the loop. That context treats
the loop in the same way, using its specifications, regardless of whether or not the loop has a body. The other side
is the loop body, that is, the implementation of each loop iteration. The verifier checks
that the loop body maintains the loop invariant and that the iterations will eventually terminate,
but if there is no loop body, the verifier is silently happy. This allows you to temporarily
postpone the authoring of the loop body until after you've made sure that the loop specification
is what you need in the context of the loop.

There is one thing that works differently for body-less loops than for loops with bodies.
It is the computation of syntactic loop targets, which become part of the loop frame
(see [Section 8.14.3](#sec-loop-framing)). For a body-less loop, the local variables
computed as part of the loop frame are the mutable variables that occur free in the
loop specification. The heap is considered a part of the loop frame if it is used
for mutable fields in the loop specification or if the loop has an explicit `modifies` clause.
The IDE will display the computed loop frame in hover text.

For example, consider

<!-- %check-verify Statements.3.expect -->
```dafny
class Cell {
  var data: int
  const K: int
}

method BodylessLoop(n: nat, c: Cell)
  requires c.K == 8
  modifies c
{
  c.data := 5;
  var a, b := n, n;
  for i := 0 to n
    invariant c.K < 10
    invariant a <= n
    invariant c.data < 10
  assert a == n;
  assert b == n;
  assert c.data == 5;
}
```

The loop specification mentions local variable `a`, and thus `a` is considered part of
the loop frame. Since what the loop invariant says about `a` is not strong enough to
prove the assertion `a == n` that follows the loop, the verifier complains about that
assertion.

Local variable `b` is not mentioned in the loop specification, and thus `b` is not
included in the loop frame. Since in-parameter `n` is immutable, it is not included
in the loop frame, either, despite being mentioned in the loop specification. For
these reasons, the assertion `b == n` is provable after the loop.

Because the loop specification mentions the mutable field `data`, the heap becomes
part of the loop frame. Since the loop invariant is not strong enough to prove the
assertion `c.data == 5` that follows the loop, the verifier complains about that
assertion. On the other hand, had `c.data < 10` not been mentioned in the loop
specification, the assertion would be verified, since field `K` is then the only
field mentioned in the loop specification and `K` is immutable.

Finally, the aggregate statement (`forall`) can also be given without a body. Such
a statement claims that the given `ensures` clause holds true for all values of
the bound variables that satisfy the given range constraint. If the statement has
no body, the program is in effect omitting the proof, much like a body-less lemma
is omitting the proof of the claim made by the lemma specification. As with the
other body-less constructs above, the verifier is silently happy with a body-less
`forall` statement, but the compiler will complain.

## 8.15. Match Statement ([grammar](#g-match-statement)) {#sec-match-statement}

Examples:
<!-- %no-check -->
```dafny

match list {
  case Nil => {}
  case Cons(head,tail) => print head;
}
match x
case 1 =>
  print x;
case 2 =>
  var y := x*x;
  print y;
case _ =>
  print "Other";
  // Any statement after is captured in this case.
```

The `match` statement is used to do case analysis on a value of an expression.
The expression may be a value of a basic type (e.g. `int`), a newtype, or
an inductive or coinductive datatype (which includes the built-in tuple types). 
The expression after the `match` keyword is called the _selector_. 
The selector is evaluated and then matched against
each clause in order until a matching clause is found.

The process of matching the selector expression against the case patterns is
the same as for match expressions and is described in
[Section 9.31.2](#sec-case-pattern).

The selector need not be enclosed in parentheses; the sequence of cases may but need not be enclosed in braces.
The cases need not be disjoint.
The cases must be exhaustive, but you can use a wild variable (`_`) or an as yet unused simple identifier to indicate "match anything".

The code below shows an example of a match statement.

<!-- %check-resolve -->
```dafny
datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)

// Return the sum of the data in a tree.
method Sum(x: Tree) returns (r: int)
{
  match x {
    case Empty => r := 0;
    case Node(t1, d, t2) =>
      var v1 := Sum(t1);
      var v2 := Sum(t2);
      r := v1 + d + v2;
  }
}
```

Note that the `Sum` method is recursive yet has no `decreases` annotation.
In this case it is not needed because Dafny is able to deduce that
`t1` and `t2` are _smaller_ (structurally) than `x`. If `Tree` had been
coinductive this would not have been possible since `x` might have been
infinite.

## 8.16. Assert statement ([grammar](#g-assert-statement)) {#sec-assert-statement}

Examples:
<!-- %no-check -->
```dafny
assert i > 0;
assert IsPositive: i > 0;
assert i > 0 by {
 ...
}
```

`Assert` statements are used to express logical propositions that are
expected to be true. Dafny will attempt to prove that the assertion
is true and give an error if the assertion cannot be proven.
Once the assertion is proved,
its truth may aid in proving subsequent deductions.
Thus if Dafny is having a difficult time verifying a method,
the user may help by inserting assertions that Dafny can prove,
and whose truth may aid in the larger verification effort,
much as lemmas might be used in mathematical proofs.

`Assert` statements are ignored by the compiler.

In the `by` form of the `assert` statement, there is an additional block of statements that provide the Dafny verifier with additional proof steps.
Those statements are often a sequence of [lemmas](#sec-lemmas), [`calc`](#sec-calc-statement) statements, [`reveal`](#sec-reveal-statements) statements or other `assert` statements,
combined with ghost control flow, ghost variable declarations and ghost update statements of variables declared in the `by` block.
The intent is that those statements be evaluated in support of proving the `assert` statement.
For that purpose, they could be simply inserted before the `assert` statement.
But by using the `by` block, the statements in the block are discarded after the assertion is proved.
As a result, the statements in the block do not clutter or confuse the solver in performing subsequent
proofs of assertions later in the program. Furthermore, by isolating the statements in the `by` block,
their purpose -- to assist in proving the given assertion -- is manifest in the structure of the code.

Examples of this form of assert are given in the section of the [`reveal`](#sec-reveal-statement) statement and in [_Different Styles of Proof_](http://leino.science/papers/krml276.html)

An assert statement may have a label, whose use is explained in [Section 8.20.1](#sec-reveal-assertions).

The attributes recognized for assert statements are discussed in [Section 11.3](#sec-verification-attributes-on-assertions).

Using `...` as the argument of the statement is deprecated.

## 8.17. Assume Statement ([grammar](#g-assume-statement)) {#sec-assume-statement}

Examples:
<!-- %no-check -->
```dafny
assume i > 0;
assume {:axiom} i > 0 ==> -i < 0;
```

The `assume` statement lets the user specify a logical proposition
that Dafny may assume to be true without proof. If in fact the
proposition is not true this may lead to invalid conclusions.

An `assume` statement would ordinarily be used as part of a larger
verification effort where verification of some other part of
the program required the proposition. By using the `assume` statement
the other verification can proceed. Then when that is completed the
user would come back and replace the `assume` with `assert`.

An `assume` statement cannot be compiled. In fact, the compiler
will complain if it finds an `assume` anywhere.

Using an `{:axiom}` attribute makes the claim that the assume statement is
OK because it is known outside the Dafny program to be true.
The verifier will not complain about it, but it is the user's 
responsibility to be absolutely sure that the proposition is
indeed true.

Using `...` as the argument of the statement is deprecated.

## 8.18. Expect Statement ([grammar](#g-expect-statement)) {#sec-expect-statement}

Examples:
<!-- %no-check -->
```dafny
expect i > 0;
expect i > 0, "i is positive";
```

The `expect` statement states a boolean expression that is
(a) assumed to be true by the verifier
and (b) checked to be true
at run-time. That is, the compiler inserts into the run-time executable a
check that the given expression is true; if the expression is false, then
the execution of the program halts immediately. If a second argument is
given, it may be a value of any type.
That value is converted to a string (just like the `print` statement)
and the string is included
in the message emitted by the program
when it halts; otherwise a default message is emitted.

Because the expect expression and optional second argument are compiled, they cannot be ghost expressions.

The `expect` statement behaves like
`assume` for the verifier, but also inserts a run-time check that the
assumption is indeed correct (for the test cases used at run-time).

Here are a few use-cases for the `expect` statement.

A) To check the specifications of external methods.

Consider an external method `Random` that takes a `nat` as input
and returns a `nat` value that is less than the input.
Such a method could be specified as
<!-- %no-check -->
```dafny
method {:extern} Random(n: nat) returns (r: nat)
  ensures r < n
```
But because there is no body for `Random` (only the external non-dafny implementation),
it cannot be verified that `Random` actually satisfies this specification.

To mitigate this situation somewhat, we can define a wrapper function, `Random'`,
that calls `Random` but in which we can put some run-time checks:
<!-- %check-resolve -->
```dafny
method {:extern} Random(n: nat) returns (r: nat)

method Random'(n: nat) returns (r: nat)
  ensures r < n
{
  r := Random(n);
  expect r < n;
}
```
Here we can verify that `Random'` satisfies its own specification,
relying on the unverified specification of `Random`.
But we are also checking at run-time that any input-output pairs for `Random`
encountered during execution
do satisfy the specification,
as they are checked by the `expect` statement.

Note, in this example, two problems still remain.
One problem is that the out-parameter of the extern `Random` has type `nat`,
but there is no check that the value returned really is non-negative.
It would be better to declare the out-parameter of `Random` to be `int` and
to include `0 <= r` in the condition checked by the `expect` statement in `Random'`.
The other problem is that `Random` surely will need `n` to be strictly positive.
This can be fixed by adding `requires n != 0` to `Random'` and `Random`.

B) Run-time testing

Verification and run-time testing are complementary
and both have their role in assuring that software does what is intended.
Dafny can produce executables
and these can be instrumented with unit tests.
Annotating a method with the `{:test}` attribute
indicates to the compiler
that it should produce target code
that is correspondingly annotated to mark the method
as a unit test (e.g., an XUnit test) in the target language.
Alternatively, the `dafny test` command will produce a main method
that invokes all methods with the `{:test}` attribute, and hence does not
depend on any testing framework in the target language.
Within such methods one might use `expect` statements (as well as `print` statements)
to insert checks that the target program is behaving as expected.

C) Debugging

While developing a new program, one work style uses proof attempts and runtime tests in combination.
If an assert statement does not prove, one might run the program with a corresponding expect statement
to see if there are some conditions when the assert is not actually true. So one might have
paired assert/expect statements:
<!-- %no-check -->
```dafny
assert _P_;
expect _P_;
```
Once the program is debugged, both statements can be removed.
Note that it is important that the `assert` come before the `expect`, because
by the verifier, the `expect` is interpreted as an `assume`, which would automatically make
a subsequent `assert` succeed.

D) Compiler tests

The same approach might be taken to assure that compiled code is behaving at run-time consistently with the statically verified code,
one can again use paired assert/expect statements with the same expression:
<!-- %no-check -->
```dafny
assert _P_;
expect _P_;
```
The verifier will check that _P_ is always true at the given point in a program
(at the `assert` statement).

At run-time, the compiler will insert checks that the same predicate,
in the `expect` statement, is true.
Any difference identifies a compiler bug.
Again the `expect` must be after the `assert`:
if the `expect` is first,
then the verifier will interpret the `expect` like an `assume`,
in which case the `assert` will be proved trivially
and potential unsoundness will be hidden.

Using `...` as the argument of the statement is deprecated.

## 8.19. Print Statement ([grammar](#g-print-statement)) {#sec-print-statement}

Examples:
<!-- %no-check -->
```dafny
print 0, x, list, array;
```

The `print` statement is used to print the values of a comma-separated
list of expressions to the console (standard-out). The generated code uses
target-language-specific idioms to perform this printing.
The expressions may of course include strings that are used
for captions. There is no implicit new line added, so to add a new
line you must include `"\n"` as part of one of the expressions.
Dafny automatically creates implementations of methods that convert values to strings
for all Dafny data types. For example,

<!-- %check-run Statements.4.expect -->
```dafny
datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)
method Main()
{
  var x : Tree := Node(Node(Empty, 1, Empty), 2, Empty);
  print "x=", x, "\n";
}
```

produces this output:

```text
x=Tree.Node(Tree.Node(Tree.Empty, 1, Tree.Empty), 2, Tree.Empty)
```

Note that Dafny does not have method overriding and there is no mechanism to
override the built-in value->string conversion.  Nor is there a way to
explicitly invoke this conversion.
One can always write an explicit function to convert a data value to a string
and then call it explicitly in a `print` statement or elsewhere.

By default, Dafny does not keep track of print effects, but this can be changed
using the `--track-print-effects` command line flag. `print` statements are allowed
only in non-ghost contexts and not in expressions, with one exception.
The exception is that a function-by-method may contain `print` statements,
whose effect may be observed as part of the run-time evaluation of such functions
(unless `--track-print-effects` is enabled).

The verifier checks that each expression is well-defined, but otherwise 
ignores the `print` statement.

<a id="print-encoding"></a>

**Note:** `print` writes to standard output.  To improve compatibility with
native code and external libraries, the process of encoding Dafny strings passed
to `print` into standard-output byte strings is left to the runtime of the
language that the Dafny code is compiled to (some language runtimes use UTF-8 in
all cases; others obey the current locale or console encoding).

In most cases, the standard-output encoding can be set before running the
compiled program using language-specific flags or environment variables
(e.g. `-Dfile.encoding=` for Java).  This is in fact how `dafny run` operates:
it uses language-specific flags and variables to enforce UTF-8 output regardless
of the target language (but note that the C++ and Go backends currently have
limited support for UTF-16 surrogates).

## 8.20. Reveal Statement ([grammar](#g-reveal-statement)) {#sec-reveal-statement}

Examples:
<!-- %no-check -->
```dafny
reveal f(), L;
```

The `reveal` statement makes available to the solver information that is otherwise not visible, as described in the following subsections.

### 8.20.1. Revealing assertions {#sec-reveal-assertions}

If an assert statement has an expression label, then a proof of that assertion is attempted, but the assertion itself
is not used subsequently.  For example, consider
<!-- %check-verify Statements.5.expect -->
```dafny
method m(i: int) {
  assert x: i == 0; // Fails
  assert i == 0; // Fails also because the x: makes the first assertion opaque
}
```
The first assertion fails. Without the label `x:`, the second would succeed because after a failing assertion, the 
assertion is assumed in the context of the rest of the program.  But with the label, the first assertion is hidden from
the rest of the program. That assertion can be _revealed_ by adding a `reveal` statement:

<!-- %check-verify Statements.6.expect -->
```dafny
method m(i: int) {
  assert x: i == 0; // Fails
  reveal x;
  assert i == 0; // Now succeeds
}
```
or
<!-- %check-verify Statements.7.expect -->
```dafny
method m(i: int) {
  assert x: i == 0; // Fails
  assert i == 0 by { reveal x; } // Now succeeds
}
```
At the point of the `reveal` statement, the labeled assertion is made visible and can be used in proving the second assertion.
In this example there is no point to labeling an assertion and then immediately revealing it. More useful are the cases where
the reveal is in an assert-by block or much later in the method body.

### 8.20.2. Revealing preconditions

In the same way as assertions, preconditions can be labeled.
Within the body of a method, a precondition is an assumption; if the precondition is labeled then that assumption is not visible in the body of the method.
A `reveal` statement naming the label of the precondition then makes the assumption visible.

Here is a toy example:
<!-- %check-verify Statements.8.expect -->
```dafny
method m(x: int, y: int) returns (z: int)
  requires L: 0 < y
  ensures z == x+y
  ensures x < z
{
  z := x + y;
}
```
The above method will not verify. In particular, the second postcondition cannot be proved.
However, if we add a `reveal L;` statement in the body of the method, then the precondition is visible 
and both postconditions can be proved.

One could also use this style:
<!-- %check-verify -->
```dafny
method m(x: int, y: int) returns (z: int)
  requires L: 0 < y
  ensures z == x+y
  ensures x < z
{
  z := x + y;
  assert x < z by { reveal L; }
}
```

The reason to possibly hide a precondition is the same as the reason to hide assertions: 
sometimes less information is better for the solver as it helps the solver focus attention on 
relevant information.

Section 7 of [http://leino.science/papers/krml276.html](http://leino.science/papers/krml276.html) provides 
an extended illustration of this technique to make all the dependencies of an `assert` explicit.

### 8.20.3. Revealing function bodies

Normally function bodies are transparent and available for constructing proofs of assertions that use those functions.
However, sometimes it is helpful to mark a function [`{:opaque}`](#sec-opaque) and treat it as an uninterpreted function, whose properties are
just its specifications.  This action limits the information available to the logical reasoning engine and may make a proof 
possible where there might be information overload otherwise.

But then there may be specific instances where the definition of that opaque function is needed. In that situation, the
body of the function can be _revealed_ using the reveal statement. Here is an example:
<!-- %check-verify Statements.9.expect -->
```dafny
opaque function f(i: int): int { i + 1 }

method m(i: int) {
  assert f(i) == i + 1;
}
```
Without the [`opaque`] modifier, the assertion is valid; with the modifier it cannot be proved because the body of the
function is not visible. However if a `reveal f();` statement is inserted before the assertion, the proof succeeds.
Note that the pseudo-function-call in the `reveal` statement is written without arguments and serves to mark `f` as a function name
instead of a label.

### 8.20.4. Revealing constants

A `const` declaration can be `opaque`. If so the value of the constant is not known in reasoning about its uses, just its type and the
fact that the value does not change. The constant's identifier can be listed in a reveal statement. In that case, like other revealed items,
the value of the constant will be known to the reasoning engine until the end of the block containing the reveal statement.

A label or locally declared name in a method body will shadow an opaque constant with the same name outside the method body,
making it unable to be revealed without using a qualified name.

## 8.21. Forall Statement ([grammar](#g-forall-statement)) {#sec-forall-statement}

Examples:
<!-- %no-check -->
```dafny
forall i | 0 <= i < a.Length {
  a[i] := 0;
}
forall i | 0 <= i < 100 {
  P(i); // P a lemma
}
forall i | 0 <= i < 100
  ensures i < 1000 {
} 
```

The `forall` statement executes the body
simultaneously for all quantified values in the specified quantifier domain.
You can find more details about [quantifier domains here](#sec-quantifier-domains).

There are several variant uses of the `forall`
statement and there are a number of restrictions.
A `forall` statement can be classified as one of the following:

* _Assign_ - the `forall` statement is used for simultaneous assignment.
The target must be an array element or an object field.
* _Call_ - The body consists of a single call to a ghost method without side effects
* _Proof_ - The `forall` has `ensure` expressions which are effectively
quantified or proved by the body (if present).

An _assign_ `forall` statement performs simultaneous assignment.
The left-hand sides must denote different l-values, unless the
corresponding right-hand sides also coincide.

The following is an excerpt of an example given by Leino in
[_Developing Verified Programs with Dafny_][leino233].
When the buffer holding the queue needs to be resized,
the `forall` statement is used to simultaneously copy the old contents
into the new buffer.

[leino233]: http://research.microsoft.com/en-us/um/people/leino/papers/krml233.pdf

<!-- %check-verify %options --relax-definite-assignment -->
```dafny
class SimpleQueue<Data(0)>
{
  ghost var Contents: seq<Data>;
  var a: array<Data>  // Buffer holding contents of queue.
  var m: int          // Index head of queue.
  var n: int          // Index just past end of queue
   
  method Enqueue(d: Data)
    requires a.Length > 0;
    requires 0 <= m <= n <= a.Length;
    modifies this, this.a;
    ensures Contents == old(Contents) + [d]
  {
    if n == a.Length {
      var b := a;
      if m == 0 { b := new Data[2 * a.Length]; }
      forall i | 0 <= i < n - m {
      	b[i] := a[m + i];
      }
      a, m, n := b, 0, n - m;
    }
    a[n], n, Contents := d, n + 1, Contents + [d];
  }
}
```

Here is an example of a _call_ `forall` statement and the
callee. This is contained in the `CloudMake-ConsistentBuilds.dfy`
test in the Dafny repository.

<!-- %no-check Too many undeclared symbols -->
```dafny
method m() {
  forall cmd', deps', e' |
       Hash(Loc(cmd', deps', e')) == Hash(Loc(cmd, deps, e)) {
    HashProperty(cmd', deps', e', cmd, deps, e);
  }
}

lemma HashProperty(cmd: Expression, deps: Expression, ext: string,
    cmd': Expression, deps': Expression, ext': string)
  requires Hash(Loc(cmd, deps, ext)) == Hash(Loc(cmd', deps', ext'))
  ensures cmd == cmd' && deps == deps' && ext == ext'
```

The following example of a _proof_ `forall` statement comes from the same file:

<!-- %no-check Too many undeclared symbols -->
```dafny
forall p | p in DomSt(stCombinedC.st) && p in DomSt(stExecC.st)
  ensures GetSt(p, stCombinedC.st) == GetSt(p, stExecC.st)
{
  assert DomSt(stCombinedC.st) <= DomSt(stExecC.st);
  assert stCombinedC.st == Restrict(DomSt(stCombinedC.st),
                                               stExecC.st);
}
```

More generally, the statement
<!-- %no-check -->
```dafny
forall x | P(x) { Lemma(x); }
```
is used to invoke `Lemma(x)` on all `x` for which `P(x)` holds. If
`Lemma(x)` ensures `Q(x)`, then the forall statement establishes
<!-- %no-check -->
```dafny
forall x :: P(x) ==> Q(x).
```

The `forall` statement is also used extensively in the de-sugared forms of
co-predicates and co-lemmas. See [datatypes](#sec-coinductive-datatypes).

## 8.22. Modify Statement ([grammar](#g-modify-statement)) {#sec-modify-statement}

The effect of the `modify` statement
is to say that some undetermined
modifications have been made to any or all of the memory
locations specified by the given [frame expressions](#sec-frame-expression).
In the following example, a value is assigned to field `x`
followed by a `modify` statement that may modify any field
in the object. After that we can no longer prove that the field
`x` still has the value we assigned to it. The now unknown values
still are values of their type (e.g. of the subset type or newtype).

<!-- %check-verify Statements.10.expect -->
```dafny
class MyClass {
  var x: int
  method N()
    modifies this
  {
    x := 18;
    modify this;
    assert x == 18;  // error: cannot conclude this here
  }
}
```

Using `...` as the argument of the statement is deprecated.

The form of the `modify` statement which includes a block
statement is also deprecated.

The [havoc assignment](#sec-havoc-statement) also sets a variable or field
to some arbitrary (but type-consistent) value. The difference is that
the havoc assignment acts on one LHS variable or memory location;
the modify statement acts on all the fields of an object.

## 8.23. Calc Statement ([grammar](#g-calc-statement)) {#sec-calc-statement}

See also: [Verified Calculations](http://research.microsoft.com/en-us/um/people/leino/papers/krml231.pdf).

The `calc` statement supports _calculational proofs_ using a language
feature called _program-oriented calculations_ (poC). This feature was
introduced and explained in the [_Verified Calculations_] paper by Leino
and Polikarpova[@LEINO:Dafny:Calc]. Please see that paper for a more
complete explanation of the `calc` statement. We here mention only the
highlights.

Calculational proofs are proofs by stepwise formula manipulation
as is taught in elementary algebra. The typical example is to prove
an equality by starting with a left-hand-side and through a series of
transformations morph it into the desired right-hand-side.

Non-syntactic rules further restrict hints to only ghost and side-effect
free statements, as well as imposing a constraint that only
chain-compatible operators can be used together in a calculation. The
notion of chain-compatibility is quite intuitive for the operators
supported by poC; for example, it is clear that "<" and ">" cannot be used within
the same calculation, as there would be no relation to conclude between
the first and the last line. See the [paper][Verified Calculations] for
a more formal treatment of chain-compatibility.

Note that we allow a single occurrence of the intransitive operator "!=" to
appear in a chain of equalities (that is, "!=" is chain-compatible with
equality but not with any other operator, including itself). Calculations
with fewer than two lines are allowed, but have no effect. If a step
operator is omitted, it defaults to the calculation-wide operator,
defined after the `calc` keyword. If that operator is omitted, it defaults
to equality.

Here is an example using `calc` statements to prove an elementary
algebraic identity. As it turns out, Dafny is able to prove this without
the `calc` statements, but the example illustrates the syntax.

<!-- %check-verify -->
```dafny
lemma docalc(x : int, y: int)
  ensures (x + y) * (x + y) == x * x + 2 * x * y + y * y
{
  calc {
    (x + y) * (x + y);
    ==
    // distributive law: (a + b) * c == a * c + b * c
    x * (x + y) + y * (x + y);
    ==
    // distributive law: a * (b + c) == a * b + a * c
    x * x + x * y + y * x + y * y;
    ==
    calc {
	    y * x;
      ==
	    x * y;
    }
    x * x + x * y + x * y + y * y;
    ==
    calc {
      x * y + x * y;
      ==
      // a = 1 * a
      1 * x * y + 1 * x * y;
      ==
      // Distributive law
      (1 + 1) * x * y;
      ==
      2 * x * y;
    }
    x * x + 2 * x * y + y * y;
  }
}
```

Here we started with `(x + y) * (x + y)` as the left-hand-side
expressions and gradually transformed it using distributive,
commutative and other laws into the desired right-hand-side.

The justification for the steps are given as comments or as
nested `calc` statements that prove equality of some sub-parts
of the expression.

The `==` operators show the relation between
the previous expression and the next. Because of the transitivity of
equality we can then conclude that the original left-hand-side is
equal to the final expression.

We can avoid having to supply the relational operator between
every pair of expressions by giving a default operator between
the `calc` keyword and the opening brace as shown in this abbreviated
version of the above calc statement:

<!-- %check-verify -->
```dafny
lemma docalc(x : int, y: int)
  ensures (x + y) * (x + y) == x * x + 2 * x * y + y * y
{
  calc == {
    (x + y) * (x + y);
    x * (x + y) + y * (x + y);
    x * x + x * y + y * x + y * y;
    x * x + x * y + x * y + y * y;
    x * x + 2 * x * y + y * y;
  }
}
```

And since equality is the default operator, we could have omitted
it after the `calc` keyword.
The purpose of the block statements or the `calc` statements between
the expressions is to provide hints to aid Dafny in proving that
step. As shown in the example, comments can also be used to aid
the human reader in cases where Dafny can prove the step automatically.


