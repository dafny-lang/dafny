# Statements
````
Stmt = ( BlockStmt | AssertStmt | AssumeStmt | ExpectStmt | PrintStmt | UpdateStmt
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
````
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
````
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
```
L: {
  var n := ReadNext();
  if n < 0  { break L; }
  DoSomething(n);
}
```
is equivalent to
```
{
  var n: ReadNext();
  if 0 <= n {
    DoSomething(n);
  }
}
```

If no label is specified and the statement lists `n`
occurrences of `break`, then the statement must be enclosed in
at least `n` levels of loops. Control continues after exiting `n`
enclosing loops. For example,

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

## Block Statement
````
BlockStmt = "{" { Stmt } "}"
````
A block statement is just a sequence of statements enclosed by curly braces.
Local variables declared in the block end their scope at the end of the block.

## Return Statement
````
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
````
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
````
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

````
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

```
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

````
    Lhs ":"
````

is diagnosed as a label in which the user forgot the **label** keyword.

## Variable Declaration Statement
````
VarDeclStatement = [ "ghost" ] "var" { Attribute }
  (
    LocalIdentTypeOptional 
    { "," { Attribute } LocalIdentTypeOptional }
    [ ":=" Rhs { "," Rhs }
    | { Attribute } ":|" [ "assume" ] 
                    Expression(allowLemma: false, allowLambda: true)
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

```
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

```
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
````
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
````
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

```
if x :| P { S } else { T }
```

has the same meaning as

```
if exists x :| P { var x :| P; S } else { T }
```

The identifiers bound by ``BindingGuard`` are ghost variables
and cannot be assigned to non-ghost variables. They are only
used in specification contexts.

Here is an example:

```
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
````
IfStmt = "if"
  ( IfAlternativeBlock
  |
    ( BindingGuard(allowLambda: true)
    | Guard
    | "..."
    )
    BlockStmt [ "else" ( IfStmt | BlockStmt ) ]
  )
````

````
IfAlternativeBlock =
   "{" { "case"
      (
        BindingGuard(allowLambda:false)
      | Expression(allowLemma: true, allowLambda: false)
      ) "=>" { Stmt } } "}" .
````

The simplest form of an `if` statement uses a guard that is a boolean
expression. It then has the same form as in C\# and other common
programming languages. For example,

```
  if x < 0 {
    x := -x;
  }
```

If the guard is an asterisk then a non-deterministic choice is made:

```
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
```
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
````
WhileStmt = "while"
  ( LoopSpecWhile WhileAlternativeBlock
  | ( Guard | "..." ) LoopSpec
      ( BlockStmt
      | "..."
      | /* go body-less */
      )
  )
````

````
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

```
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

```
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

```
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

```
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

```
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
````
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

```
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
````
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

## Assume Statement
````
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

````
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

Paired `assert` and `expect` statements 
(with `assert` before `expect`) checking the
same expression can be used to do runtime checking before there is a successful proof
of an assert statement (or to help debug one that is unprovable).[^expect]

[^expect]: Aside from difficulties in constructing a successful proof, 
paired (consecutive) `assert` and `expect` statements in a program should always produce the 
same results, except if the compiler is faulty. Of course, the `expect` statement only checks the 
test cases for which the program is run.

Using `...` as the argument of the statement is part of module refinement, as described [here](#sec-module-refinement).

<!--
Describe where refinement is described.

If the proposition is `...` then (TODO: what does this mean?).
-->

## Print Statement
````
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

```
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
````
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

```
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

```
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

```
forall p | p in DomSt(stCombinedC.st) && p in DomSt(stExecC.st)
  ensures GetSt(p, stCombinedC.st) == GetSt(p, stExecC.st)
{
  assert DomSt(stCombinedC.st) <= DomSt(stExecC.st);
  assert stCombinedC.st == Restrict(DomSt(stCombinedC.st), 
                                               stExecC.st);
}
```

More generally, the statement
```
forall x | P(x) { Lemma(x); }
```
is used to invoke `Lemma(x)` on all `x` for which `P(x)` holds. If
`Lemma(x)` ensures `Q(x)`, then the forall statement establishes
```
forall x :: P(x) ==> Q(x).
```

The `forall` statement is also used extensively in the de-sugared forms of
co-predicates and co-lemmas. See section [#sec-co-inductive-datatypes].

## Modify Statement
````
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

```
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

```
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

```
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
````
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

```
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

```
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
````
SkeletonStmt =
  "..."
  ["where" Ident {"," Ident } ":="
    Expression(allowLemma: false, allowLambda: true)
    {"," Expression(allowLemma: false, allowLambda: true) }
  ] ";"
````
-->

