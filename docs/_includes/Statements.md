# Statements
````grammar
Stmt = ( BlockStmt | AssertStmt | AssumeStmt | ExpectStmt | PrintStmt
  | UpdateStmt | UpdateFailureStmt
  | VarDeclStatement | IfStmt | WhileStmt | MatchStmt | ForallStmt
  | CalcStmt | ModifyStmt | LabeledStmt_ | BreakStmt_ | ReturnStmt
  | RevealStmt | YieldStmt
  )
````
<!--
Grammar has SkeletonStmt
Added RevealStmt

Describe where refinement is described.

| SkeletonStmt
-->

Many of Dafny's statements are similar to those in traditional
programming languages, but a number of them are significantly different.
This grammar production shows the different kinds of Dafny statements.
They are described in subsequent sections.

## Labeled Statement
````grammar
LabeledStmt_ = "label" LabelName ":" Stmt
````
A labeled statement is just the keyword `label` followed by an identifier
which is the label, followed by a colon and a statement. The label may be
referenced in a break statement  that is within the labeled statement
to transfer control to the location after
the labeled statement.
The label is not allowed to be the same as any previous dominating
label.

The label may also be used in an [`old` expression](#sec-old-expression). In this case the label
must have been encountered during the control flow in route to the `old`
expression. That is, again, the label must dominate the use of the label.

## Break Statement
````grammar
BreakStmt_ = "break" ( LabelName | { "break" } ) ";"
````
A break statement provides a means to transfer control
in a way different than the usual nested control structures.
There are two forms of break statement: with and without a label.

If a label is used, the break statement must be enclosed in a statement
with that label and the result is to transfer control to the statement
after the labeled statement. For example, such a break statement can be
used to exit a sequence of statements in a block statement before
reaching the end of the block.

For example,
```dafny
L: {
  var n := ReadNext();
  if n < 0  { break L; }
  DoSomething(n);
}
```
is equivalent to
```dafny
{
  var n: ReadNext();
  if 0 <= n {
    DoSomething(n);
  }
}
```
var i := 0;
while i < 10 {
  var j := 0;
  while j < 10 {
    var k := 0;
    while k < 10 {
      if (j + k == 15) break break;
      k := k + 1;
    }
    j := j + 1;
  }
  // control continues here after the break
  i := i + 1;
}
```

If no label is specified and the statement lists `n`
occurrences of `break`, then the statement must be enclosed in
at least `n` levels of loops. Control continues after exiting `n`
enclosing loops. For example,

```dafny
var i := 0;
while i < 10 {
  var j := 0;
  while j < 10 {
    var k := 0;
    while k < 10 {
      if (j + k == 15) break break;
      k := k + 1;
    }
    j := j + 1;
  }
  // control continues here after the break
  i := i + 1;
}
```

## Block Statement
````grammar
BlockStmt = "{" { Stmt } "}"
````
A block statement is just a sequence of statements enclosed by curly braces.
Local variables declared in the block end their scope at the end of the block.

## Return Statement
````grammar
ReturnStmt = "return" [ Rhs { "," Rhs } ] ";"
````
A return statement can only be used in a method. It is used
to terminate the execution of the method.

To return a value from a method, the value is assigned to one
of the named out-parameters sometime before a return statement.
In fact, the out-parameters act very much like local variables,
and can be assigned to more than once. Return statements are
used when one wants to return before reaching the end of the
body block of the method.

Return statements can be just the return keyword (where the current value
of the out-parameters are used), or they can take a list of expressions to
return. If a list is given, the number of expressions given must be the same
as the number of named out-parameters. These expressions are
evaluated, then they are assigned to the out-parameters, and then the
method terminates.

## Yield Statement
````grammar
YieldStmt = "yield" [ Rhs { "," Rhs } ] ";"
````

A yield statement can only be used in an iterator.
See section [Iterator types](#sec-iterator-types) for more details
about iterators.

The body of an iterator is a _co-routine_. It is used
to yield control to its caller, signaling that a new
set of values for the iterator's yield parameters (if any)
are available. Values are assigned to the yield parameters
at or before a yield statement.
In fact, the yield parameters act very much like local variables,
and can be assigned to more than once. Yield statements are
used when one wants to return new yield parameter values
to the caller. Yield statements can be just the
**yield** keyword (where the current value of the yield parameters
are used), or they can take a list of expressions to yield.
If a list is given, the number of expressions given must be the
same as the number of named return yield parameters.
These expressions are then evaluated, then they are
assigned to the yield parameters, and then the iterator
yields.

## Update and Call Statements {#sec-update-and-call-statement}
````grammar
UpdateStmt =
    Lhs
    ( {Attribute} ";"
    |If more than one
left-hand side is used, these must denote different l-values, unless the
corresponding right-hand sides also denote the same value.
     { "," Lhs }
     ( ":=" Rhs { "," Rhs }
     | ":|" [ "assume" ]
               Expression(allowLemma: false, allowLambda: true)
     )
     ";"
    | ":"
    )
````

````grammar
CallStmt_ =
    [ Lhs { , Lhs } ":=" ] Lhs ";"
````

The update statement serves several logical purposes.


1) The form

```
Lhs {Attribute} ";"
```
is assumed to be a call to a method with no out-parameters.

2) The form

```
    [ Lhs { , Lhs } ":=" ] Lhs ";"
```
can occur in the ``UpdateStmt`` grammar when there is a single Rhs that
takes the special form of a ``Lhs`` that is a call;
that is, this form matches the grammar of a ``CallStmt_``, in which the ``Lhs`` after
the `:=` references a method and the arguments to it, corresponding to a
method call or a new allocation with an initializing method.
This is the only case
where the number of left-hand sides can be different than the number of
right-hand sides in the ``UpdateStmt``. In that case the number of
left-hand sides must match the number of out-parameters of the
method that is called or there must be just one ``Lhs`` to the left of
the `:=`, which then is assigned a tuple of the out-parameters.
Note that the result of a method call is not allowed to be used as an argument of
another method call, as if it were an expression.

3) If no call is involved, the ``UpdateStmt`` can be a parallel
assignment of right-hand-side values to the left-hand sides. For example,
`x,y := y,x` swaps the values of `x` and `y`. If more than one
left-hand side is used, these must denote different l-values, unless the
corresponding right-hand sides also denote the same value. There must
be an equal number of left-hand sides and right-hand sides in this case.
Of course, the most common case will have only one
``Rhs`` and one ``Lhs``.

4) The form that uses "`:|`" assigns some values to the left-hand side
variables such that the boolean expression on the right hand side
is satisfied. This can be used to make a choice as in the
following example where we choose an element in a set.

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
exist which satisfy the condition.

In addition, as the choice is arbitrary,
assignment statements using `:|` may be non-deterministic
when executed.

Note that the form

````grammar
    Lhs ":"
````

is diagnosed as a label in which the user forgot the **label** keyword.

## Update with Failure Statement (`:-`)
````grammar
UpdateFailureStmt  =
    [ Lhs { "," Lhs } ]
    ":-"
    [ "expect" ]
    Expression(allowLemma: false, allowLambda: false) { "," Rhs }
````

A `:-` statement is similar to a `:=` statement, but allows for immediate return if a failure is detected.
This is a language feature somewhat analogous to exceptions in other languages.

An update-with-failure statement uses _failure-compatible_ types.
A failure-compatible type is a type that has the following members (each with no in-parameters and one out-parameter):

 * a function method `IsFailure()` that returns a `bool`
 * a function method `PropagateFailure()` that returns a value assignable to the first out-parameter of the caller
 * an optional method or function `Extract()`

A failure-compatible type with an `Extract` member is called _value-carrying_.


To use this form of update,

 * the caller must have a first out-parameter whose type matches the output of `PropagateFailure` applied to the first output of the callee
 * if the RHS of the update-with-failure statement is a method call, the first out-parameter of the callee must be failure-compatible
 * if instead the RHS of the update-with-failure statement is one or more expressions, the first of these expressions must be a value with a failure-compatible type
 * if the failure-compatible type of the RHS does not have an `Extract` member,
then the LHS of the `:-` statement has one less expression than the RHS
(or than the number of out-parameters from the method call)
 * if the failure-compatible type of the RHS does have an `Extract` member,
then the LHS of the `:-` statement has the same number of expressions as the RHS
(or as the number of out-parameters from the method call)
and the type of the first LHS expression must be assignable from the return type of the `Extract` member
* the `IsFailure` and `PropagateFailure` methods may not be ghost
* the LHS expression assigned the output of the `Extract` member is ghost precisely if `Extract` is ghost

### Failure compatible types

A simple failure-compatible type is the following:
```dafny
{% include Example-Fail1.dfy %}
```

A commonly used alternative that carries some value information is something like this generic type:
```dafny
{% include Example-Fail2.dfy %}
```


### Simple status return with no other outputs

The simplest use of this failure-return style of programming is to have a method call that just returns a non-value-carrying `Status` value:
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
then that return value is forgotten and execution proceeds normally with the statements following the call of `callee` in the body of `Caller`.

The desugaring of the `:- Callee(i);` statement is
```dafny
var tmp;
tmp := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
In this and subsequent examples of desugaring, the `tmp` variable is a new, unique variable, unused elsewhere in the calling member.

### Status return with additional outputs

The example in the previous subsection affects the program only through side effects or the status return itself.
It may well be convenient to have additional out-parameters, as is allowed for `:=` updates;
these out-parameters behave just as for `:=`.
Here is an example:

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

   * If `Callee` returns a failure value as its first output, then the other outputs are assigned, the _caller's_ first out-parameter (here `rr`) is assigned the value of `PropagateFailure`, and the caller returns.
   * If `Callee` returns a non-failure value as its first output, then the other outputs are assigned and the
caller continues execution as normal.

The desugaring of the `j, k :- Callee(i);` statement is
```dafny
var tmp;
tmp, j, k := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```


### Failure-returns with additional data

The failure-compatible return value can carry additional data as shown in the `Outcome<T>` example above.
In this case there is a (first) LHS l-value to receive this additional data.

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
```dafny
var tmp;
tmp, k := Callee(i);
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
j := tmp.Extract();
```

### RHS with expression list

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
   * if the type of `r` is value-carrying, then `r.Extract()` is assigned to the first LHS value of the `:-` statement
(if `r` is not value-carrying, then the corresponding LHS l-value is omitted)
   * execution of the caller's body continues with the statement following the `:-` statement.

A RHS with a method call cannot be mixed with a RHS containing multiple expressions.

For example, the desugaring of
```dafny
method m(Status r) returns (rr: Status) {
  var j, k;
  j, k :- r, 7;
  ...
}
```
is
```dafny
var j, k;
var tmp;
tmp, k := r, 7;
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
### Failure with initialized declaration.

The `:-` syntax can also be used in initalization, as in
```dafny
var s :- M();
```
This is equivalent to
```dafny
var s;
s :- M();
```
with the semantics as described above.

### Expect alternative

In any of the above described uses of `:-`, the `:-` token may be followed immediately by the keyword `expect`.
This keyword states that the RHS evaluation is expected to be successful:
if the failure-compatible value is a failure, then the program halts immediately (precisely as with the `expect` statement);
if the return value is not a failure, the semantics is as described in previous sub-sections.

The equivalent desugaring replaces
```dafny
if tmp.IsFailure() {
  rr := tmp.PropagateFailure();
  return;
}
```
with
```dafny
expect !tmp.IsFailure(), tmp;
```

### Key points

There are several points to note.

 * The first out-parameter of the callee is special.
It has a special type and that type indicates that the value is inspected to see if an immediate return
from the caller is warranted.
This type is often a datatype, as shown in the examples above, but it may be any type with the appropriate members.
 * The restriction on the type of caller's first out-parameter is
just that it must be possible (perhaps through generic instantiation and type inference, as in these examples) for `PropagateFailure` applied to the failure-compatible output from the callee to produce a value of the caller's first out-parameter type.
If the caller's first out-parameter type is failure-compatible (which it need not be),
 then failures can be propagated up the call chain.
 * In the statement `j, k :- callee(i);`,
 when the callee's return value has an `Extract` member,
the type of `j` is not the type of the first out-parameter of `callee`.
Rather it is a type assignable from the output type of `Extract` applied to the first out-value of `callee`.
 * A method like `callee` with a special first out-parameter type can still be used in the normal way:
`r, k := callee(i)`.
Now `r` gets the first output value from callee, of type `Status` or `Outcome<nat>` in the examples above.
No special semantics or exceptional control paths apply.
Subsequent code can do its own testing of the value of `r`
and whatever other computations or control flow are desired.
 * The caller and callee can have any (positive) number of output arguments,
as long as the callee's first out-parameter has a failure-compatible type
and the caller's first out-parameter type matches `PropagateFailure`.
 * If there is more than one LHS, the LHSs must denote different l-values, unless the RHS is a list of expressions and the corresponding RHS values are equal.
 * The LHS l-values are evaluated before the RHS method call,
in case the method call has side-effects or return values that modify the l-values prior to assignments being made.

It is important to note the connection between the failure-compatible types used in the caller and callee,
if they both use them.
They do not have to be the same type, but they must be closely related,
as it must be possible for the callee's `PropagateFailure` to return a value of the caller's failure-compatible type.
In practice this means that one such failure-compatible type should be used for an entire program.
If a Dafny program uses a library shared by multiple programs, the library should supply such a type and it should be used by all the client programs (and, effectively, all Dafny libraries).
It is also the case that it is inconvenient to mix types such as `Outcome` and `Status` above within the same program.
If there is a mix of failure-compatible types, then the program will need to use `:=` statements and code for
explicit handling of failure values.


### Failure returns and exceptions

The `:-` mechanism is like the exceptions used in other programming languages, with some similarities and differences.

 * There is essentially just one kind of 'exception' in Dafny,
the variations of the failure-compatible data type.
 * Exceptions are passed up the call stack whether or not intervening methods are aware of the possibility of an exception,
that is, whether or not the intervening methods have declared that they throw exceptions.
Not so in Dafny: a failure is passed up the call stack only if each caller has a failure-compatible first out-parameter, is itself called in a `:-` statement, and returns a value that responds true to `IsFailure()`.
 * All methods that contain failure-return callees must explicitly handle those failures
using either `:-` statements or using `:=` statements with a LHS to receive the failure value.

## Variable Declaration Statement
````grammar
VarDeclStatement = [ "ghost" ] "var" { Attribute }
  (
    LocalIdentTypeOptional
    { "," { Attribute } LocalIdentTypeOptional }
    [ ":=" Rhs { "," Rhs }
    | { Attribute } ":|" [ "assume" ]
                    Expression(allowLemma: false, allowLambda: true)
    | ":-" [ "expect" ] Expression { "," Rhs }
    ]
  |
    "(" CasePattern { "," CasePattern } ")"
    ":=" Expression(allowLemma: false, allowLambda: true)
  )
  ";"
````

A ``VarDeclStatement`` is used to declare one or more local variables in
a method or function. The type of each local variable must be given
unless its type can be inferred, either from a given initial value, or
from other uses of the variable. If initial values are given, the number
of values must match the number of variables declared.

Note that the type of each variable must be given individually. The following code

```dafny
var x, y : int;
```
does not declare both `x` and `y` to be of type `int`. Rather it will give an
error explaining that the type of `x` is underspecified if it cannot be
inferred from uses of x.

What follows the ``LocalIdentTypeOptional`` optionally combines the variable
declarations with an update statement (cf. [Update and Call Statement](#sec-update-and-call-statement)).
If the Rhs is a call, then any variable receiving the value of a
formal ghost out-parameter will automatically be declared as ghost, even
if the **ghost** keyword is not part of the variable declaration statement.

The left-hand side can also contain a tuple of patterns which will be
matched against the right-hand-side. For example:

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

## Guards
````grammar
Guard = ( "*"
        | "(" "*" ")"
        | Expression(allowLemma: true, allowLambda: true)
        )
````
Guards are used in `if` and `while` statements as boolean expressions. Guards
take two forms.

The first and most common form is just a boolean expression.

The second form is either `*` or `(*)`. These have the same meaning. An
unspecified boolean value is returned. The value returned
may be different each time it is executed.

## Binding Guards
````grammar
BindingGuard(allowLambda) =
  IdentTypeOptional { "," IdentTypeOptional } { Attribute }
  ":|" Expression(allowLemma: true, allowLambda)
````

``IfStmt``s can also take a ``BindingGuard``.
It checks if there exist values for the given variables that satisfy the given expression.
If so, it binds some satisfying values to the variables and proceeds
into the "then" branch; otherwise it proceeds with the "else" branch,
where the bound variables are not in scope.

In other words, the statement

```dafny
if x :| P { S } else { T }
```

has the same meaning as

```dafny
if exists x :| P { var x :| P; S } else { T }
```

The identifiers bound by ``BindingGuard`` are ghost variables
and cannot be assigned to non-ghost variables. They are only
used in specification contexts.

Here is an example:

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

## If Statement
````grammar
IfStmt = "if"
  ( IfAlternativeBlock
  | "{" IfAlternativeBlock "}"
  |
    ( BindingGuard(allowLambda: true)
    | Guard
    | "..."
    )
    BlockStmt [ "else" ( IfStmt | BlockStmt ) ]
  )
````

````grammar
IfAlternativeBlock =
      { "case"
      (
        BindingGuard(allowLambda:false)
      | Expression(allowLemma: true, allowLambda: false)
      ) "=>" { Stmt } } .
````

The simplest form of an `if` statement uses a guard that is a boolean
expression. It then has the same form as in C\# and other common
programming languages. For example,

```dafny
  if x < 0 {
    x := -x;
  }
```

If the guard is an asterisk then a non-deterministic choice is made:

```dafny
  if * {
    print "True";
  } else {
    print "False";
  }
```

The `if` statement using the `IfAlternativeBlock` form is similar to the
`if ... fi` construct used in the book "A Discipline of Programming" by
Edsger W. Dijkstra. It is used for a multi-branch `if`.

For example:
```dafny
  if {
    case x <= y => max := y;
    case y <= x => max := x;
  }
```

In this form, the expressions following the `case` keyword are called
_guards_. The statement is evaluated by evaluating the guards in an
undetermined order until one is found that is `true` and the statements
to the right of `=>` for that guard are executed. The statement requires
at least one of the guards to evaluate to `true`.

## While Statement
````grammar
WhileStmt = "while"
  ( LoopSpecWhile ( WhileAlternativeBlock | "{" WhileAlternativeBlock "}" )
  | ( Guard | "..." ) LoopSpec
      ( BlockStmt
      | "..."
      | /* go body-less */
      )
  )
````

````grammar
WhileAlternativeBlock =
   "{"
   { "case" Expression(allowLemma: true, allowLambda: false)
   "=>" { Stmt } }
   "}
````

Loops need _loop specifications_ (``LoopSpec`` in the grammar) in order for Dafny to prove that
they obey expected behavior. In some cases Dafny can infer the loop specifications by analyzing the code,
so the loop specifications need not always be explicit.
These specifications are described in the [section on Loop Specifications](#sec-loop-specification).

The `while` statement is Dafny's only loop statement. It has two general
forms.

The first form is similar to a while loop in a C-like language. For
example:

```dafny
  var i := 0;
  while i < 5 {
    i := i + 1;
  }
```

In this form, the condition following the `while` is one of these:

* A boolean expression. If true it means execute one more
iteration of the loop. If false then terminate the loop.
* An asterisk (`*`), meaning non-deterministically yield either
`true` or `false` as the value of the condition

<!--
Keep the following commented out until we decide a better
place to put it.

* An ellipsis (`...`), which makes the while statement a _skeleton_
`while` statement. TODO: What does that mean?

The _body_ of the loop is usually a block statement, but it can also
be a _skeleton_, denoted by ellipsis, or missing altogether.
TODO: Wouldn't a missing body cause problems? Isn't it clearer to have
a block statement with no statements inside?
-->

The second form uses the `WhileAlternativeBlock`. It is similar to the
`do ... od` construct used in the book "A Discipline of Programming" by
Edsger W. Dijkstra. For example:

```dafny
  while
    decreases if 0 <= r then r else -r;
  {
    case r < 0 =>
      r := r + 1;
    case 0 < r =>
      r := r - 1;
  }
```
For this form, the guards are evaluated in some undetermined order
until one is found that is true, in which case the corresponding statements
are executed. If none of the guards evaluates to true, then the
loop execution is terminated.
k

## Loop Specifications {#sec-loop-specification}
For some simple loops, such as those mentioned previously, Dafny can figure
out what the loop is doing without more help. However, in general the user
must provide more information in order to help Dafny prove the effect of
the loop. This information is provided by a ``LoopSpec``. A
``LoopSpec`` provides information about invariants, termination, and
what the loop modifies.
For additional tutorial information see [@KoenigLeino:MOD2011] or the
[online Dafny tutorial](http://rise4fun.com/Dafny/tutorial/Guide).

### Loop Invariants

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
beginning of the loop, we must show that executing the loop body once
makes the invariant hold again. Dafny can only know upon analyzing the
loop body what the invariants say, in addition to the loop guard (the
loop condition). Just as Dafny will not discover properties of a method
on its own, it will not know any but the most basic properties of a loop
are preserved unless it is told via an invariant.

### Loop Termination

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
(cf. Section [Well-Founded Orders](#sec-well-founded-orders).

Many times, an integral value (natural or plain integer) is the quantity
that decreases, but other things that can be used as well. In the case of
integers, the bound is assumed to be zero. For example, the following is
a proper use of `decreases` on a loop:

```dafny
  while 0 < i
    invariant 0 <= i
    decreases i
  {
    i := i - 1;
  }
```

Here Dafny has all the ingredients it needs to prove termination. The
variable i gets smaller each loop iteration, and is bounded below by
zero. This is fine, except the loop is backwards from most loops, which
tend to count up instead of down. In this case, what decreases is not the
counter itself, but rather the distance between the counter and the upper
bound. A simple trick for dealing with this situation is given below:

```dafny
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
```

This is actually Dafny's guess for this situation, as it sees `i < n` and
assumes that `n - i` is the quantity that decreases. The upper bound of the
loop invariant implies that `0 <= n – i`, and gives Dafny a lower bound on
the quantity. This also works when the bound `n` is not constant, such as
in the binary search algorithm, where two quantities approach each other,
and neither is fixed.

If the **decreases** clause of a loop specified "*", then no
termination check will be performed. Use of this feature is sound only with
respect to partial correctness.

### Loop Framing
In some cases we also must specify what memory locations the loop body
is allowed to modify. This is done using a `modifies` clause.
See the discussion of framing in methods for a fuller discussion.

TO BE WRITTEN

## Match Statement
````grammar
MatchStmt = "match" Expression(allowLemma: true, allowLambda: true)
  ( "{" { CaseStatement } "}"
  | { CaseStatement }
  )

CaseStatement = CaseBinding_ "=>" { Stmt }
````

The `match` statement is used to do case analysis on a value of inductive or co-inductive datatype (which includes the built-in tuple types), a base type, or newtype. The expression after the `match` keyword is called the _selector_. The expression is evaluated and then matched against
each clause in order until a matching clause is found.

The identifier after the `case` keyword in a case clause, if present,
must be either the name of one of the datatype's constructors (when the selector is a value of a datatype), a literal (when the selector is a value of a base type or a newtype), or a
variable, in which case the clause matches any constructors.
If the constructor takes parameters then a parenthesis-enclosed
list of patterns must follow the
constructor. There must be as many patterns as the constructor
has parameters. If the optional type is given it must be the same
as the type of the corresponding parameter of the constructor.
If no type is given then the type of the corresponding parameter
is the type assigned to the identifier. If the identifier
represents a variable, it cannot be applied to arguments.
 If the variable is not used
in a case, it can be replaced by an underscore.

When an inductive value that was created using constructor
expression `C1(v1, v2)` is matched against a case clause
`C2(x1, x2`), there is a match provided that `C1` and `C2` are the
same constructor. In that case `x1` is bound to value `v1` and
`x2` is bound to `v2`. The identifiers in the case pattern
are not mutable. Here is an example of the use of a `match` statement.

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

## Assert Statement
````grammar
AssertStmt =
    "assert" { Attribute }
    ( Expression(allowLemma: false, allowLambda: true)
    | "..."
    ) ";"
````

`Assert` statements are used to express logical proposition that are
expected to be true. Dafny will attempt to prove that the assertion
is true and give an error if the assertion cannot be provenb.
Once the assertion is proved,
its truth is to aid in proving following deductions.
Thus if Dafny is having a difficult time verifying a method,
the user may help by inserting assertions that Dafny can prove,
and whose truth may aid in the larger verification effort,
much as lemmas might be used in mathematical proofs.

Using `...` as the argument of the statement is part of module refinement, as described [here](#sec-module-refinement).

TO BE WRITTEN - assert by statements

## Assume Statement
````grammar
AssumeStmt =
    "assume" { Attribute }
    ( Expression(allowLemma: false, allowLambda: true)
    | "..."
    ) ";"
````

The `assume` statement lets the user specify a logical proposition
that Dafny may assume to be true without proof. If in fact the
proposition is not true this may lead to invalid conclusions.

An `assume` statement would ordinarily be used as part of a larger
verification effort where verification of some other part of
the program required the proposition. By using the `assume` statement
the other verification can proceed. Then when that is completed the
user would come back and replace the `assume` with `assert`.

An `assume` statement cannot be compiled. In fact, the compiler
will complain if it finds an **assume** anywhere where it has not
been replaced through a refinement step.

Using `...` as the argument of the statement is part of module refinement, as described [here](#sec-module-refinement).

## Expect Statement

````grammar
ExpectStmt =
    "expect" { Attribute }
    ( Expression(allowLemma: false, allowLambda: true)
    | "..."
    )
    [ "," Expression(allowLemma: false, allowLambda: true) ]
    ";"
````

The `expect` statement states a boolean expression that is
(a) assumed to be true by the verifier
and (b) checked to be true
at run-time. That is, the compiler inserts into the run-time executable a
check that the given expression is true; if the expression is false, then
the execution of the program halts immediately. If a second argument is
given, it may be a value of any type.
That value is converted to a string (just like the `print` statement)
and  the string is included
in the message emitted by the program
when it halts; otherwise a default message is emitted.

Because the expect expression and optional second argument are compiled, they cannot be ghost expressions.

`assume` statements are ignored at run-time. The `expect` statement behaves like
`assume` for the verifier, but also inserts a run-time check that the
assumption is indeed correct (for the test cases used at run-time).

Here are a few use-cases for the `expect` statement.

A) To check the specifications of external methods.

Consider an external method `Random` that takes a `nat` as input
and returns a `nat` value that is less than the input.
Such a method could be specified as
```dafny
method {:extern} Random(n: nat) returns (r: nat)
  ensures r < n
```
But because there is no body for `Random` (only the external non-dafny implementation),
it cannot be verified that `Random` actually satisfies this specification.

To mitigate this situation somewhat, we can define a wrapper function, `Random'`,
that calls `Random` but in which we can put some run-time checks:
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

Note, in this example, two problems are still remaining.
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
Within that method one might use `expect` statements (as well as `print` statements)
to insert checks that the target program is behaving as expected.

C) Compiler tests

If one wants to assure that compiled code is behaving at run-time consistently with the statically verified code,
one can use paired assert/expect statements with the same expression:
```dafny
assert _P_;
expect _P_;
```
The verifier will check that _P_ is always true at the given point in a program
(at the `assert` statement).

At run-time, the compiler will insert checks that the same predicate,
in the `expect` statement is true.
Any difference identifies a compiler bug.
Note that the `expect` must be after the `assert`.
If the `expect` is first,
then the verifier will interpret the `expect` like an `assume`,
in which case the `assert` will be proved trivially
and potential unsoundness will be hidden.

Using `...` as the argument of the `expect` statement is part of module refinement, as described [here](#sec-module-refinement).

<!--
Describe where refinement is described.

If the proposition is `...` then (TODO: what does this mean?).
-->

## Print Statement
````grammar
PrintStmt =
    "print" Expression(allowLemma: false, allowLambda: true)
    { "," Expression(allowLemma: false, allowLambda: true) } ";"
````

The `print` statement is used to print the values of a comma-separated
list of expressions to the console. The generated code uses
target-language-specific idioms to perform this printing.
The expressions may of course include strings that are used
for captions. There is no implicit new line added, so to add a new
line you should include `"\n"` as part of one of the expressions.
Dafny automatically creates implementations of methods that convert values to strings
for all Dafny data types. For example,

```dafny
datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)
method Main()
{
  var x : Tree := Node(Node(Empty, 1, Empty), 2, Empty);
  print "x=", x, "\n";
}
```

produces this output:

```
x=Tree.Node(Tree.Node(Tree.Empty, 1, Tree.Empty), 2, Tree.Empty)
```

Note that Dafny does not have method overriding and there is no mechanism to
override the built-in value->string conversion.  Nor is there a way to
explicitly invoke this conversion.

## Forall Statement
````grammar
ForallStmt = "forall"
  ( "(" [ QuantifierDomain ] ")"
  | [ QuantifierDomain ]
  )
  { ForAllEnsuresClause_ }
  [ BlockStmt ]
````

The `forall` statement executes the body
simultaneously for all quantified values in the specified range.
There are several variant uses of the `forall`
statement and there are a number of restrictions.

In particular, a `forall` statement can be classified as one of the following:

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

```dafny
class {:autocontracts} SimpleQueue<Data>
{
  ghost var Contents: seq<Data>;
  var a: array<Data>  // Buffer holding contents of queue.
  var m: int          // Index head of queue.
  var n: int          // Index just past end of queue
  ...
  method Enqueue(d: Data)
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

```dafny
forall cmd', deps', e' |
       Hash(Loc(cmd', deps', e')) == Hash(Loc(cmd, deps, e)) {
  HashProperty(cmd', deps', e', cmd, deps, e);
}

lemma HashProperty(cmd: Expression, deps: Expression, ext: string,
    cmd': Expression, deps': Expression, ext': string)
  requires Hash(Loc(cmd, deps, ext)) == Hash(Loc(cmd', deps', ext'))
  ensures cmd == cmd' && deps == deps' && ext == ext'
```

The following example of a _proof_ `forall` statement comes from the same file:

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
```dafny
forall x | P(x) { Lemma(x); }
```
is used to invoke `Lemma(x)` on all `x` for which `P(x)` holds. If
`Lemma(x)` ensures `Q(x)`, then the forall statement establishes
```dafny
forall x :: P(x) ==> Q(x).
```

The `forall` statement is also used extensively in the de-sugared forms of
co-predicates and co-lemmas. See section [#sec-co-inductive-datatypes].

## Modify Statement
````grammar
ModifyStmt =
  "modify" { Attribute }
  ( FrameExpression(allowLemma: false, allowLambda: true)
    { "," FrameExpression(allowLemma: false, allowLambda: true) }
  | "..."
  )
  ( BlockStmt | ";" )
````

The `modify` statement has two forms which have two different
purposes.

When the `modify` statement ends with a semi-colon rather than
a block statement its effect is to say that some undetermined
modifications have been made to any or all of the memory
locations specified by the [frame expressions](#sec-frame-expressions).
In the following example, a value is assigned to field `x`
followed by a `modify` statement that may modify any field
in the object. After that we can no longer prove that the field
`x` still has the value we assigned to it.

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

When the `modify` statement is followed by a block statement,
we are instead specifying what can be modified in that
block statement. Namely, only memory locations specified
by the frame expressions of the block `modify` statement
may be modified. Consider the following example.

```dafny
class ModifyBody {
  var x: int
  var y: int
  method M0()
    modifies this
  {
    modify {} {
      x := 3;  // error: violates modifies clause of the modify statement
    }
  }

  method M1()
    modifies this
  {
    modify {} {
      var o := new ModifyBody;
      o.x := 3;  // fine
    }
  }

  method M2()
    modifies this
  {
    modify this {
      x := 3;
    }
  }
```

```dafny
  method M3()
    modifies this
  {
    var k: int;
    modify {} { k := 4; } // fine. k is local
  }
}
```

The first `modify` statement in the example has an empty
frame expression so it cannot modify any memory locations.
So an error is reported when it tries to modify field `x`.

The second `modify` statement also has an empty frame
expression. But it allocates a new object and modifies it.
Thus we see that the frame expressions on a block `modify`
statement only limit what may be modified in already allocated
memory. It does not limit what may be modified in
new memory that is allocated within the block.

The third `modify` statement has a frame expression that
allows it to modify any of the fields of the current object,
so the modification of field `x` is allowed.

Finally, the fourth example shows that the restrictions imposed by
the modify statement do not apply to local variables, only those
that are heap-based.

## Calc Statement
````grammar
CalcStmt = "calc" { Attribute } [ CalcOp ] "{" CalcBody "}"
CalcBody = { CalcLine [ CalcOp ] Hints }
CalcLine = Expression(allowLemma: false, allowLambda: true) ";"
Hints = { ( BlockStmt | CalcStmt ) }
CalcOp =
  ( "==" [ "#" "["
           Expression(allowLemma: true, allowLambda: true) "]" ]
  | "<" | ">"
  | "!=" | "<=" | ">="
  | "<==>" | "==>" | "<=="
  )
````

[Verified Calculations]: http://research.microsoft.com/en-us/um/people/leino/papers/krml231.pdf

The `calc` statement supports _calculational proofs_ using a language
feature called _program-oriented calculations_ (poC). This feature was
introduced and explained in the [_Verified Calculations_] paper by Leino
and Polikarpova[@LEINO:Dafny:Calc]. Please see that paper for a more
complete explanation of the `calc` statement. We here mention only the
highlights.

Calculational proofs are proofs by stepwise formula manipulation
as is taught in elementary algebra. The typical example is to prove
an equality by starting with a left-hand-side, and through a series of
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

The justification for the steps are given as comments, or as
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

```dafny
calc == {
  (x + y) * (x + y);
  x * (x + y) + y * (x + y);
  x * x + x * y + y * x + y * y;
  x * x + x * y + x * y + y * y;
  x * x + 2 * x * y + y * y;
}
```

And since equality is the default operator, we could have omitted
it after the `calc` keyword.
The purpose of the block statements or the `calc` statements between
the expressions is to provide hints to aid Dafny in proving that
step. As shown in the example, comments can also be used to aid
the human reader in cases where Dafny can prove the step automatically.

## Reveal Statement

TO BE WRITTEN

<!--
Move to discussion of refinement.

## Skeleton Statement
````grammar
SkeletonStmt =
  "..."
  ["where" Ident {"," Ident } ":="
    Expression(allowLemma: false, allowLambda: true)
    {"," Expression(allowLemma: false, allowLambda: true) }
  ] ";"
````
-->
