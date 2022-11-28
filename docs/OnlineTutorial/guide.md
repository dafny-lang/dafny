<p></p> <!-- avoids duplicate title -->

# Getting Started with Dafny: A Guide

## Introduction

Dafny is a language that is designed to make it easy to
write correct code. This means correct in the sense of not having any runtime
errors, but also correct in actually doing what the programmer intended it to
do. To accomplish this, Dafny relies on high-level annotations to reason about
and prove correctness of code. The effect of a piece of code can be given abstractly,
using a natural, high-level expression of the desired behavior, which is easier
and less error prone to write than the implementation code itself.
 Dafny then generates a proof that the code
matches the annotations (assuming they are correct, of course!). Dafny lifts the
burden of writing bug-free *code* into that of writing bug-free *annotations*.
This is often easier than writing the code, because annotations are shorter and
more direct. For example, the following fragment of annotation in Dafny says
that every element of the array is strictly positive:

<!-- %no-check -->
```dafny
forall k: int :: 0 <= k < a.Length ==> 0 < a[k]
```

This says that for all integers `k`
that are indices into the array, the value at that index is greater than zero.
By writing these annotations, one is confident that the code is correct.
Further, the very act of writing the annotations can help one understand what the
code is doing at a deeper level.

In addition to proving a correspondence to user supplied
annotations, Dafny proves that there are no run time errors, such as index out
of bounds, null dereferences, division by zero, etc. This guarantee is a
powerful one, and is a strong case in and of itself for the use of Dafny and
tools like it. Dafny also proves the termination of code, except in specially
designated loops.

Let's get started writing some Dafny programs.

## Methods

Dafny resembles a typical imperative programming language in
many ways. There are methods, variables, types, loops, if statements, arrays,
integers, and more. One of the basic units of any Dafny program is the *method*.
A method is a piece of imperative, executable code. In other languages, they
might be called procedures, or functions, but in Dafny the term "function" is
reserved for a different concept that we will cover later. A method is declared
in the following way:

<!-- %check-verify guide.1.expect -->
```dafny
method Abs(x: int) returns (y: int)
{
  ...
}
```

This declares a method called "`Abs`"
which takes a single integer parameter, called "`x`", and
returns a single integer, called "`y`". Note that the types
are required for each parameter and return value, and follow each name after a
colon (`:`). Also, the return values are named, and there
can be multiple return values, as in this code:

<!-- %check-verify guide.2.expect -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
{
  ... ...
}
```

The method body is the code contained within the braces,
which until now has been cleverly represented as "`...`"
(which is *not* Dafny syntax). The body consists of a
series of *statements*, such as the familiar imperative
assignments, `if` statements, loops, other method calls, `return` statements, etc.
For example, the `MultipleReturns` method may be
implemented as:

<!-- %check-verify -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
{
  more := x + y;
  less := x - y;
  // comments: are not strictly necessary.
}
```

Assignments do not use "`=`", but
rather "`:=`". (In fact, as Dafny uses "`==`"
for equality, there is no use of a single equals sign in Dafny expressions.) Simple statements
must be followed by a semicolon, and whitespace and comments (`//` and `/**/`) are ignored. To
return a value from a method, the value is assigned to one of the named return
values sometime before a `return` statement. In fact, the return values act very
much like local variables, and can be assigned to more than once. The input
parameters, however, are read only. `return` statements are used when one wants
to return before reaching the end of the body block of the method. Return
statements can be just the `return` keyword (where the current value of the out
parameters are used), or they can take a list of values to return. There are
also compound statements, such as `if` statements. `if` statements do not require
parentheses around the boolean condition, and act as one would expect:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

One caveat is that they always need braces around the
branches, even if the branch only contains a single statement (compound or
otherwise). Here the `if` statement checks whether `x` is less than
zero, using the familiar comparison operator syntax, and returns the absolute value as
appropriate. (Other comparison operators are `<=`, `>`, `>=`, `!=`
and `==`, with the expected meaning. See the reference
for more on operators.)

## Pre- and Postconditions

None of what we have seen so far has any specifications: the
code could be written in virtually any imperative language (with appropriate
considerations for multiple return values). The real power of Dafny comes from
the ability to annotate these methods to specify their behavior. For example,
one property that we observe with the `Abs` method is that the result is always
greater than or equal to zero, regardless of the input. We could put this
observation in a comment, but then we would have no way to know whether the
method actually had this property. Further, if someone came along and changed
the method, we wouldn't be guaranteed that the comment was changed to match.
With annotations, we can have Dafny prove that the property we claim of the method
is true. There are several ways to give annotations, but some of the most
common, and most basic, are method *pre-*
and *postconditions*.

This property of the `Abs` method, that the result is always
non-negative, is an example of a postcondition: it is something that is true
after the method returns. Postconditions, declared with the `ensures`
keyword, are given as part of the method's declaration, after the return values
(if present) and before the method body. The keyword is followed by the boolean
expression. Like an `if` or `while`
condition and most specifications, a postcondition is always a boolean
expression: something that can be *true* or *false*. In
the case of the `Abs` method, a reasonable postcondition is the following:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

You can see here why return values are given names. This
makes them easy to refer to in the postcondition of a method. When the
expression is true, we say that the postcondition *holds*.
The postcondition must hold for every invocation of the function, and for every
possible return point (including the implicit one at the end of the function body).
In this case, the only property we are expressing is that the return value is
always at least zero.

Sometimes there are multiple properties that we would like
to establish about our code. In this case, we have two options. We can either
join the two conditions together with the boolean "and" operator (`&&`), or
we can write multiple `ensures` specifications. The
latter is basically the same as the former, but it separates distinct
properties. For example, the return value names from the `MultipleReturns`
method might lead one to guess the following postconditions:

<!-- %check-verify guide.3.expect -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x
  ensures x < more
{
  more := x + y;
  less := x - y;
}
```

The postcondition can also be written:

<!-- %check-verify guide.4.expect -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x && x < more
{
  more := x + y;
  less := x - y;
}
```

or even:

<!-- %check-verify guide.5.expect -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}
```

because of the chaining comparison operator syntax in Dafny.
(In general, most of the comparison operators can be chained, but only "in one
direction", i.e. not mixing "greater than" and "less than". See the reference for
details.)

The first way of expressing the postconditions separates
the "less" part from the "more" part, which may be desirable. Another thing to
note is that we have included one of the input parameters in the
postcondition. This is useful because it allows us to relate the input and
output of the method to one another (this works because input parameters are
read only, and so are the same at the end as they were at the beginning).

Dafny actually rejects this program, claiming that the first
postcondition does not hold (i.e. is not true). This means that Dafny wasn't
able to prove that this annotation holds every time the method returns. In
general, there are two main causes for Dafny verification errors: specifications
that are inconsistent with the code, and situations where it is not "clever"
enough to prove the required properties. Differentiating between these two
possibilities can be a difficult task, but fortunately, Dafny and the Boogie/Z3
system on which it is based are pretty smart, and will prove matching code and specifications
with a minimum of fuss.

In this situation, Dafny is correct in saying there is an
error with the code. The key to the problem is that `y`
is an integer, so it can be negative. If `y` is negative (or zero), then `more`
can actually be smaller than or equal to `x`. Our method will not work as intended
unless `y` is strictly larger than zero. This is precisely the idea of
a *precondition*. A precondition is similar to a postcondition, except
that it is something that must be true *before*
a method is called. When you call a method, it is your job to establish (make
true) the preconditions, something Dafny will enforce using a proof. Likewise,
when you write a method, you get to assume the preconditions, but you must
establish the postconditions. The caller of the method then gets to assume
that the postconditions hold after the method returns.

Preconditions have their own keyword, `requires`.
We can give the necessary precondition to `MultipleReturns`
as below:

<!-- %check-verify -->
```dafny
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}
```

Like postconditions, multiple preconditions can be written
either with the boolean "and" operator (`&&`), or
by multiple `requires` keywords. Traditionally, `requires`
precede `ensures` in the source code, though this is not strictly necessary
(although the order of the `requires` and `ensures` annotations with respect to
others of the same type can sometimes matter, as we will see later). With the
addition of this condition, Dafny now verifies the code as correct, because
this assumption is all that is needed to guarantee the code in the method body
is correct.

**Exercise 0.**
  *Write a method `Max` that takes two integer parameters and returns
  their maximum. Add appropriate annotations and make sure your code
  verifies.*

<!-- %check-verify guide.6.expect -->
```dafny
method Max(a: int, b: int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
  // Hint: there are many ways to write this.
{
  // fill in the code here
}
```

Not all methods necessarily have preconditions. For
example, the `Abs` method we have already seen is defined for all integers, and
so has no preconditions (other than the trivial requirement that its argument
is an integer, which is enforced by the type system). Even though it has no
need of preconditions, the `Abs` function as it stands now is not very useful.
To investigate why, we need to make use of another kind of annotation, the *assertion*.

## Assertions

Unlike pre- and postconditions, an assertion is placed
somewhere in the middle of a method. Like the previous two annotations, an
assertion has a keyword, `assert`, followed by the
boolean expression and the semicolon that terminates simple
statements. An assertion says that a particular
expression always holds when control reaches that part of the code. For
example, the following is a trivial use of an assertion inside a dummy method:

<!-- %check-verify -->
```dafny
method Testing()
{
  assert 2 < 3;
  // Try "asserting" something that is not true.
  // What does Dafny output?
}
```

Dafny proves this method correct, as `2` is always less than
`3`. Asserts have several uses, but chief among them is checking whether your
expectations of what is true at various points is actually true. You can use this
to check basic arithmetical facts, as above, but they can also be used in more
complex situations. Assertions are a powerful tool for debugging annotations,
by checking what Dafny is able to prove about your code. For example, we can
use it to investigate what Dafny knows about the `Abs` function.

To do this, we need one more concept: local variables. Local
variables behave exactly as you would expect, except maybe for a few issues
with shadowing. (See the reference for details.) Local variables are declared
with the `var` keyword, and can optionally have type
declarations. Unlike method parameters, where types are required, Dafny can
infer the types of local variables in almost all situations. This is an example
of an initialized, explicitly typed variable declaration:

<!-- %check-verify -->
```dafny
method m()
{
  var x: int := 5;
}
```

The type annotation can be dropped in this case:

<!-- %check-verify -->
```dafny
method m()
{
  var x := 5;
}
```

Multiple variables can be declared at once:

<!-- %check-verify -->
```dafny
method m()
{
  var x, y, z: bool := 1, 2, true;
}
```

Explicit type declarations only apply to the immediately
preceding variable, so here the `bool` declaration only
applies to `z`, and not `x` or `y`, which are
both inferred to be `int`s.
We needed variables because we want to talk about the return value of the `Abs`
method. We cannot put `Abs` inside a specification directly, as the method could
change memory state, among other problems. So we capture the return value of a
call to `Abs` as follows:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
}
```

This is an example of a situation where we can ask Dafny
what it knows about the values in the code, in this case `v`.
We do this by adding assertions, like the one above. Every time Dafny
encounters an assertion, it tries to prove that the condition holds for all
executions of the code. In this example, there is only one control path through
the method, and Dafny is able to prove the annotation easily because it is
exactly the postcondition of the `Abs` method. `Abs` guarantees that the return
value is non-negative, so it trivially follows that `v`, which is this value, is
non-negative after the call to `Abs`.

**Exercise 1.**
  *Write a test method that calls your `Max` method from Exercise 0
  and then asserts something about the result.*

<!-- %check-resolve -->
```dafny
method Max(a: int, b:int) returns (c: int)
  // Use your code from Exercise 0
method Testing() {
  // Assert some things about Max. Does it operate as you expect?
  // If it does not, can you think of a way to fix it?
}
```

But we know something stronger about the `Abs` method. In
particular, for non-negative `x`, `Abs(x) == x`. Specifically, in the
above program, the value of `v` is 3. If we try adding an assertion (or
changing the existing one) to say:

<!-- %check-verify guide.7.expect -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  assert v == 3;
}
```

we find that Dafny cannot prove our assertion, and gives an
error. The reason this happens is that Dafny "forgets" about the body of every
method except the one it is currently working on. This simplifies Dafny's job
tremendously, and is one of the reasons it is able to operate at reasonable
speeds. It also helps us reason about our programs by breaking them apart and so
we can analyze each method in isolation (given the annotations for the other
methods). We don't care at all what happens inside each method when we call it,
as long as it satisfies its annotations. This works because Dafny will prove
that all the methods satisfy their annotations, and refuse to compile our code
until they do.

For the `Abs` method, this means that the only thing Dafny
knows in the Testing method about the value returned from `Abs` is what the postconditions
say about it, *and nothing more*. This means that Dafny won't know the
nice property about `Abs` and non-negative integers unless we tell it by putting
this in the postcondition of the `Abs` method. Another way to look at it is to
consider the method annotations (along with the type of the parameters and
return values) as fixing the behavior of the method. Everywhere the method is
used, we assume that it is any one of the conceivable method(s) that satisfies the pre- and
postconditions. In the `Abs` case, we might have written:

<!-- %check-verify guide.8.expect -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  y := 0;
}
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  // this still does not verify, but now it is actually not true:
  assert v == 3;
}
```

This method satisfies the postconditions, but clearly the
program fragment:

<!-- %check-verify guide.9.expect -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  y := 0;
}
method Testing()
{
  var v := Abs(3);
  assert 0 <= v;
  assert v == 3;
}
```

would not be true in this case. Dafny is considering, in an
abstract way, all methods with those annotations. The mathematical absolute
value certainly is such a method, but so are all methods that return a positive
constant, for example. We need stronger postconditions to eliminate these
other possibilities, and "fix" the method down to exactly the one we want. We
can partially do this with the following:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures 0 <= x ==> y == x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

This expresses exactly the property we discussed before,
that the absolute value is the same for non-negative integers. The second
ensures is expressed via the implication operator, which basically says that
the left hand side implies the right in the mathematical sense (it binds more
weakly than boolean "and" and comparisons, so the above says `0 <= x` implies `y == x`).
The left and right sides must both be boolean expressions.

The postcondition says that after `Abs` is called, if the
value of `x` was non-negative, then `y`
is equal to `x`. One caveat of the implication is that it
is still true if the left part (the antecedent) is false. So the second
postcondition is trivially true when `x` is negative. In
fact, the only thing that the annotations say when `x` is
negative is that the result, `y`, is positive. But this
is still not enough to fix the method, so we must add another postcondition,
to make the following complete annotation covering all cases:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

These annotations are enough to require that our method
actually computes the absolute value of `x`. These postconditions are
not the only way to express this property. For example, this is a different,
and somewhat shorter, way of saying the same thing:

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  ensures 0 <= y && (y == x || y == -x)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

In general, there can be many ways to write down a given property. Most of the
time it doesn't matter which one you pick, but a good choice can make it easier
to understand the stated property and verify that it is correct.

But we still have an issue: there seems to be a lot of duplication. The body of the method
is reflected very closely in the annotations. While this is correct code, we
want to eliminate this redundancy. As you might guess, Dafny provides a means
of doing this: functions.

**Exercise 2.**
  *Using a precondition, change `Abs` to say it can only be called on
  negative values. Simplify the body of `Abs` into just one return
  statement and make sure the method still verifies.*

<!-- %check-verify -->
```dafny
method Abs(x: int) returns (y: int)
  // Add a precondition here.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  // Simplify the body to just one return statement
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

**Exercise 3.**
  *Keeping the postconditions of `Abs` the same as above, change the
  body of `Abs` to just `y := x + 2`. What precondition do you need to
  annotate the method with in order for the verification to go
  through? What precondition do you need if the body is `y := x + 1`?
  What does that precondition say about when you can call the method?*

<!-- %check-verify guide.10.expect -->
```dafny
method Abs(x: int) returns (y: int)
  // Add a precondition here so that the method verifies.
  // Don't change the postconditions.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y:= x + 2;
}
method Abs2(x: int) returns (y: int)
  // Add a precondition here so that the method verifies.
  // Don't change the postconditions.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y:= x + 1;
}
```

## Functions

<!-- %no-check -->
```dafny
function abs(x: int): int
{
  ...
}
```

This declares a function called `abs`
which takes a single integer, and returns an integer (the second `int`).
Unlike a method, which can have all sorts of statements
in its body, a function body must consist of exactly one expression, with the
correct type. Here our body must be an integer expression. In order to
implement the absolute value function, we need to use an *`if` expression*. An `if`
expression is like the ternary operator in other languages.

<!-- %check-verify -->
```dafny
function abs(x: int): int
{
  if x < 0 then -x else x
}
```

Obviously, the condition must be a boolean expression, and
the two branches must have the same type. You might wonder why anyone would
bother with functions, if they are so limited compared to methods. The power of
functions comes from the fact that they can be *used directly in specifications*.
So we can write:

<!-- %check-verify -->
```dafny
function abs(x: int): int
{
  if x < 0 then -x else x
}
method m()
{
  assert abs(3) == 3;
}
```

In fact, not only can we write this statement directly
without capturing to a local variable, we didn't even need to write all the
postconditions that we did with the method (though functions can and do have
pre- and postconditions in general). The limitations of functions are
precisely what let Dafny do this. Unlike methods, Dafny does not forget the
body of a function when considering other functions. So it can expand the
definition of `abs` in the above assertion and determine that the result is
actually `3`.

**Exercise 4.**
  *Write a **function** `max` that returns the larger of two given
  integer parameters. Write a test method using an `assert` that
  checks that your function is correct.*

<!-- %check-resolve -->
```dafny
function max(a: int, b: int): int
{
  0 // Fill in an expression here.
}
method Testing() {
  // Add assertions to check max here.
}
```

One caveat of functions is that not only can they appear in
annotations, they can only appear in annotations. One cannot write:

<!-- %no-check -->
```dafny
  var v := abs(3);
```

as this is not an annotation. Functions are never part of
the final compiled program, they are just tools to help us verify our code.
Sometimes it is convenient to use a function in real code, so one can define a
`function method`, which can be called from real code. Note
that there are restrictions on what functions can be function methods (See the
reference for details).

**Exercise 5.**
  *Change your test method from Exercise 4 to capture the value of
  `max` to an out-parameter, and then do the checks from Exercise 4 using
  the variable. Dafny will reject this program because you are calling
  `max` from real code. Fix this problem using a `function method`.*

<!-- %check-resolve -->
```dafny
function max(a: int, b: int): int
{
  0 // Use your code from Exercise 4
}
method Testing() returns (r: int) {
  // Add assertions to check max here. Be sure to capture it to the out-parameter
  r := 0;
}
```

**Exercise 6.**
  *Now that we have an `abs` function, change the postcondition of
  method `Abs` to make use of `abs`. After confirming the method still
  verifies, change the body of `Abs` to also use `abs`. (After doing
  this, you will realize there is not much point in having a method
  that does exactly the same thing as a function method.)*

<!-- %check-verify -->
```dafny
function abs(x: int): int
{
  if x < 0 then -x else x
}
method Abs(x: int) returns (y: int)
  // Use abs here, then confirm the method still verifies.
{
  // Then change this body to also use abs.
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

Unlike methods, functions can appear in expressions. Thus we
can do something like implement the mathematical Fibonacci function:

<!-- %check-verify -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
```

Here we use `nat`s, the type of
natural numbers (non-negative integers), which is often more convenient than
annotating everything to be non-negative. It turns out that we could make this
function a function method if we wanted to. But this would be extremely slow,
as this version of calculating the Fibonacci numbers has exponential
complexity. There are much better ways to calculate the Fibonacci function. But
this function is still useful, as we can have Dafny prove that a fast version
really matches the mathematical definition. We can get the best of both worlds:
the guarantee of correctness and the performance we want.

We can start by defining a method like the following:

<!-- %check-verify guide.11.expect -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  ...
}
```

We haven't written the body yet, so Dafny will complain that
our postcondition doesn't hold. We need an algorithm to calculate the `n`<sup>th</sup>
Fibonacci number. The basic idea is to keep a counter and repeatedly calculate adjacent pairs
of Fibonacci numbers until the desired number is reached. To do this, we need a loop. In Dafny, this is done
via a *`while` loop*. A while loop looks like the following:

<!-- %check-verify -->
```dafny
method m(n: nat)
{
  var i := 0;
  while i < n
  {
    i := i + 1;
  }
}
```

This is a trivial loop that just increments `i` until it reaches `n`. This will form
the core of our loop to calculate Fibonacci numbers.

## Loop Invariants

`while` loops present a problem for Dafny. There is no way for
Dafny to know in advance how many times the code will go around the loop. But
Dafny needs to consider all paths through a program, which could include going
around the loop any number of times. To make it possible for Dafny to work with
loops, you need to provide *loop invariants*, another kind of annotation.

A loop invariant is an expression that holds upon entering a
loop and after every execution of the loop body. It captures something that is
invariant, i.e. does not change, about every step of the loop. Now, obviously
we are going to want to change variables, etc. each time around the loop, or we
wouldn't need the loop. Like pre- and postconditions, an invariant is a *property* that is
preserved for each execution of the loop, expressed using the same boolean
expressions we have seen. For example, we see in the above loop that if `i`
starts off positive, then it stays positive. So we can add the invariant, using
its own keyword, to the loop:

<!-- %check-verify -->
```dafny
method m(n: nat)
{
  var i := 0;
  while i < n
    invariant 0 <= i
  {
    i := i + 1;
  }
}
```

When you specify an invariant, Dafny proves two things: the
invariant holds upon entering the loop and it is preserved by the loop. By
preserved, we mean that assuming that the invariant holds at the beginning of
the loop, we must show that executing the loop body once makes the invariant
hold again. Dafny can only know upon analyzing the loop body what the
invariants say, in addition to the loop guard (the loop condition). Just as
Dafny will not discover properties of a method on its own, it will not know any
but the most basic properties of a loop are preserved unless it is told via an
invariant.

In our example, the point of the loop is to build up the
Fibonacci numbers one (well, two) at a time until we reach the desired number. After
we exit the loop, we will have that `i == n`, because `i` will stop being
incremented when it reaches `n`. We can use our assertion trick to check to see if Dafny
sees this fact as well:

<!-- %check-verify guide.12.expect -->
```dafny
method m(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i
  {
    i := i + 1;
  }
  assert i == n;
}
```

We find that this assertion fails. As far as Dafny knows, it
is possible that `i` somehow became much larger than `n` at some point during the loop.
All it knows after the loop exits (i.e. in the code after the loop) is that the loop guard
failed and the invariants hold. In this case, this amounts to `n <= i`
and `0 <= i`. But this is not enough to guarantee that
`i == n`, just that `n <= i`.
Somehow we need to eliminate the possibility of `i`
exceeding `n`. One first guess for solving this problem
might be the following:

<!-- %check-verify guide.13.expect -->
```dafny
method m(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i < n
  {
    i := i + 1;
  }
}
```

This does not verify, as Dafny complains that the invariant
is not preserved (also known as not maintained) by the loop. We want to be able to
say that after the loop exits, then all the invariants hold. Our invariant
holds for every execution of the loop *except*
for the very last one. Because the loop body is executed only when the loop
guard holds, in the last iteration `i` goes from `n - 1` to `n`, but does not increase
further, as the loop exits. Thus, we have only omitted exactly one case from
our invariant, and repairing it is relatively easy:

<!-- %check-verify -->
```dafny
method m(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
}
```

Now we can say both that `n <= i`
from the loop guard and `0 <= i <= n` from the
invariant, which allows Dafny to prove the assertion `i == n`.
The challenge in picking loop invariants is finding one that is preserved
by the loop, but also that lets you prove what you need after the loop
has executed.

**Exercise 7.**
  *Change the loop invariant to `0 <= i <= n+2`. Does the loop still
  verify? Does the assertion `i == n` after the loop still verify?*

<!-- %check-verify -->
```dafny
method m(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n  // Change this. What happens?
  {
    i := i + 1;
  }
  assert i == n;
}
```


**Exercise 8.**
  *With the original loop invariant, change the loop guard from
  `i < n` to `i != n`. Do the loop and the assertion after the loop
  still verify? Why or why not?*

<!-- %check-verify -->
```dafny
method m(n: nat)
{
  var i: int := 0;
  while i < n  // Change this. What happens?
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  assert i == n;
}
```


In addition to the counter, our algorithm called for a pair
of numbers which represent adjacent Fibonacci numbers in the sequence.
Unsurprisingly, we will have another invariant or two to relate these numbers
to each other and the counter. To find these invariants, we employ a common
Dafny trick: working backwards from the postconditions.

Our postcondition for the Fibonacci method is that the
return value `b` is equal to `fib(n)`.
But after the loop, we have that `i == n`, so we need `b == fib(i)`
at the end of the loop. This might make a good
invariant, as it relates something to the loop counter. This observation is
surprisingly common throughout Dafny programs. Often a method is just a
loop that, when it ends, makes the postcondition true by having a counter
reach another number, often an argument or the length of an array or sequence.
So we have that the variable `b`, which is conveniently
our out parameter, will be the current Fibonacci number:

<!-- %no-check -->
```dafny
  invariant b == fib(i)
```

We also note that in our algorithm, we can compute any Fibonacci
number by keeping track of a pair of numbers and summing them to get the next
number. So we want a way of tracking the previous Fibonacci number, which we
will call `a`. Another invariant will express that
number's relation to the loop counter. The invariants are:

<!-- %no-check -->
```dafny
  invariant a == fib(i - 1)
```

At each step of the loop, the two values are summed to get
the next leading number, while the trailing number is the old leading number.
Using a parallel assignment, we can write a loop that performs this operation:

<!-- %check-verify guide.14.expect -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
```

Here `a` is the trailing number and `b` is the leading number.
The parallel assignment means that the entire right hand side is
calculated before the assignments to the
variables are made. Thus `a` will get the old value of `b`, and `b`
will get the sum of the two
old values, which is precisely the behavior we want.

We also have made a change to the loop counter `i`. Because we
also want to track the trailing number, we can't start the counter at zero, as
otherwise we would have to calculate a negative Fibonacci number. The problem
with doing this is that the loop counter invariant may not hold when we enter
the loop. The only problem is when `n` is zero. This can
be eliminated as a special case, by testing for this condition at the beginning
of the loop. The completed Fibonacci method becomes:

<!-- %check-verify -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
```

Dafny no longer complains about the loop invariant not
holding, because if `n` were zero, it would return before reaching the loop.
Dafny is also able to use the loop invariants to prove that after the loop, `i == n`
and `b == fib(i)`, which together imply the postcondition, `b == fib(n)`.

**Exercise 9.**
  *The `ComputeFib` method above is more complicated than
  necessary. Write a simpler program by not introducing `a` as the
  Fibonacci number that precedes `b`, but instead introducing a
  variable `c` that succeeds `b`. Verify your program is correct
  according to the mathematical definition of Fibonacci.*

<!-- %check-verify -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)  // Do not change this postcondition
{
  // Change the method body to instead use c as described.
  // You will need to change both the initialization and the loop.
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
```


**Exercise 10.**
  *Starting with the completed `ComputeFib` method above, delete the
  `if` statement and initialize `i` to `0`, `a` to `1`, and `b` to
  `0`.  Verify this new program by adjusting the loop invariants to
  match the new behavior.*

<!-- %check-verify guide.15.expect -->
```dafny
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  var a := 1;
  b := 0;
  while i < n
    // Fill in the invariants here.
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
```

One of the problems with using invariants is that it is easy
to forget to have the loop *make progress*, i.e. do work at each step. For
example, we could have omitted the entire body of the loop in the previous
program. The invariants would be correct, because they are still true upon
entering the loop, and since the loop doesn't change anything, they would be
preserved by the loop. We know that *if* we exit the loop, then we can assume the
negation of the guard and the invariants, but this says nothing about what
happens if we never exit the loop. Thus we would like to make sure the loop ends
at some point, which gives us a stronger correctness guarantee
(the technical term is *total correctness*).

## Termination

Dafny proves that code terminates, i.e. does not loop forever, by
using `decreases` annotations. For many things, Dafny is able to guess the right
annotations, but sometimes it needs to be made explicit. In fact, for all of the
code we have seen so far, Dafny has been able to do this proof on its own,
which is why we haven't seen the `decreases` annotation explicitly yet. There
are two places Dafny proves termination: loops and recursion. Both of these
situations require either an explicit annotation or a correct guess by Dafny.

A `decreases` annotation, as its name suggests, gives Dafny
an expression that decreases with every loop iteration or recursive call.
There are two conditions that Dafny needs to verify when using a `decreases`
expression: that the expression actually gets smaller and that it is bounded.
Many times, an integral value (natural or plain integer) is the quantity that
decreases, but other things that can be used as well. (See the reference for
details.) In the case of integers, the bound is assumed to be zero. For
example, the following is a proper use of `decreases` on a loop (with its own
keyword, of course):

<!-- %check-verify -->
```dafny
method m ()
{
  var i := 20;
  while 0 < i
    invariant 0 <= i
    decreases i
  {
    i := i - 1;
  }
}
```

Here Dafny has all the ingredients it needs to prove
termination. The variable `i` gets smaller each loop iteration and is bounded
below by zero. This is fine, except the loop is backwards from most loops,
which tend to count up instead of down. In this case, what decreases is not the
counter itself, but rather the distance between the counter and the upper
bound. A simple trick for dealing with this situation is given below:

<!-- %check-verify -->
```dafny
method m()
{
  var i, n := 0, 20;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}
```

This is actually Dafny's guess for this situation, as it
sees `i < n` and assumes that `n - i`
is the quantity that decreases. The upper bound of the loop invariant implies
that `0 <= n – i`, and gives Dafny a lower bound on
the quantity. This also works when the bound `n` is not
constant, such as in the binary search algorithm, where two quantities approach
each other, and neither is fixed.

**Exercise 11.**
  *In the loop above, the invariant `i <= n` and the negation of the
  loop guard allow us to conclude `i == n` after the loop (as we
  checked previously with an `assert`. Note that if the loop guard
  were instead written as `i != n` (as in Exercise 8), then the
  negation of the guard immediately gives `i == n` after the loop,
  regardless of the loop invariant. Change the loop guard to `i != n`
  and delete the invariant annotation. Does the program verify? What
  happened?*

<!-- %check-verify guide.16.expect -->
```dafny
method m()
{
  var i, n := 0, 20;
  while i != n
    decreases n - i
  {
    i := i + 1;
  }
}
```

The other situation that requires a termination proof is
when methods or functions are recursive. Similarly to looping forever, these
methods could potentially call themselves forever, never returning to their
original caller. When Dafny is not able to guess the termination condition, an
explicit decreases clause can be given along with pre- and postconditions, as
in the unnecessary annotation for the fib function:

<!-- %check-verify -->
```dafny
function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}
```

As before, Dafny can guess this condition on its own, but
sometimes the decreasing condition is hidden within a field of an
object or somewhere else where
Dafny cannot find it on its own, and it requires an explicit annotation.

There is a longer tutorial on termination [here](./Termination).

## Arrays

All that we have considered is fine for toy functions and
little mathematical exercises, but it really isn't helpful for real programs.
So far we have only considered a handful of values at a time in local
variables. Now we turn our attention to arrays of data. Arrays are a built-in
part of the language, with their own type, `array<T>`,
where `T` is another type;
the companion type `array?<T>` is the type of possibly-null arrays.
That is, `array?<T>` includes all references to one-dimensional arrays of
element type `T` (i.e., `array<T>`) and the null reference.
For now we only consider
arrays of integers, with type `array<int>`.
Arrays have a built-in length field, `a.Length`.
Element access uses the standard bracket syntax and indexes from
zero, so `a[3]` is preceded by the 3 elements `a[0]`,
`a[1]`, and `a[2]`, in that order.
All array accesses must be proven to be within bounds, which is part of Dafny's
no-runtime-errors safety guarantee. Because bounds checks are proven
at verification time, no runtime checks need to be made. To create a new array,
it must be allocated with the `new` keyword, but for now
we will only work with methods that take a previously allocated array as an
argument.

One of the most basic things we might want to do with an
array is search through it for a particular key, and return the index of a
place where we can find the key if it exists. We have two outcomes for a
search, with a different correctness condition for each. If the algorithm
returns an index (i.e. non-negative integer), then the key should be present at
that index. This might be expressed as follows:

<!-- %check-resolve -->
```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
{
  // Can you write code that satisfies the postcondition?
  // Hint: you can do it with one statement.
}
```

The array index here is safe because the implication
operator is *short circuiting*. Short circuiting means
if the left part is false, then
the implication is already true regardless of the truth value of the second
part, and thus it does not need to be evaluated. Using the short circuiting
property of the implication operator, along with the boolean "and" (`&&`),
which is also short circuiting, is a common
Dafny practice. The condition `index < a.Length` is
necessary because otherwise the method could return a large integer which is
not an index into the array. Together, the short circuiting behavior means that
by the time control reaches the array access, `index`
must be a valid index.

If the key is not in the array, then we would like the method
to return a negative number. In this case, we want to say that the method did
not miss an occurrence of the key; in other words, that the key is not in the
array. To express this property, we turn to another common Dafny tool:
quantifiers.

## Quantifiers

A quantifier in Dafny most often takes the form of a <span
class=Code>forall</span> expression, also called a universal quantifier. As its
name suggests, this expression is true if some property holds for all elements
of some set. For now, we will consider the set of integers. An example
universal quantifier, wrapped in an assertion, is given below:

<!-- %check-verify-warn guide.17.expect -->
```dafny
method m()
{
  assert forall k :: k < k + 1;
}
```

A quantifier introduces a temporary name for each element of
the set it is considering. This is called the bound variable, in this case `k`.
The bound variable has a type, which is almost always inferred
rather than given explicitly and is usually `int` anyway.
(In general, one can have any number of bound variables, a topic we will return
to later.) A pair of colons (`::`) separates the bound
variable and its optional type from the quantified property (which must be of
type `bool`). In this case, the property is that adding
one to any integer makes a strictly larger integer. Dafny is able to prove this
simple property automatically. Generally it is not very useful to quantify over
infinite sets, such as all the integers. Instead, quantifiers are typically
used to quantify over all elements in an array or data structure. We do this
for arrays by using the implication operator to make the quantified property
trivially true for values which are not indices:

<!-- %no-check -->
```dafny
  assert forall k :: 0 <= k < a.Length ==> ...a[k]...;
```

This says that some property holds for each element of the
array. The implication makes sure that `k` is actually a valid index into the
array before evaluating the second part of the expression. Dafny can use this
fact not only to prove that the array is accessed safely, but also to reduce the
set of integers it must consider to only those that are indices into the array.

With a quantifier, saying the key is not in the array is
straightforward:

<!-- %no-check -->
```dafny
  forall k :: 0 <= k < a.Length ==> a[k] != key
```

Thus our method postconditions become:

<!-- %check-resolve -->
```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  // There are many ways to fill this in. Can you write one?
}
```

Note that because `a` has type `array<int>`, it is implicitly non-null.

We can fill in the body of this method in a number of ways,
but perhaps the easiest is a linear search, implemented below:

<!-- %check-verify guide.18.expect -->
```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}
```

As you can see, we have omitted the loop invariants on the
`while` loop, so Dafny gives us a verification error on one of the
postconditions. The reason we get an error is that Dafny does not know that
the loop actually covers all the elements. In order to convince Dafny of this,
we have to write an invariant that says that everything before the current
index has already been looked at (and are not the key). Just like the
postcondition, we can use a quantifier to express this property:

<!-- %check-verify guide.19.expect -->
```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}
```

This says that everything before, but excluding, the current
index is not the key. Notice that upon entering the loop, `i`
is zero, so the first part of the implication is always false, and thus the
quantified property is always true. This common situation is known as
*vacuous truth*: the
quantifier holds because it is quantifying over an empty set of objects. This
means that it is true when entering the loop. We test the value of the array
before we extend the non-key part of the array, so Dafny can prove that this
invariant is preserved. One problem arises when we try to add this invariant:
Dafny complains about the index being out of range for the array access within
the invariant.

This code does not verify because there is no invariant on `index`, so
it could be greater than the length of the array. Then the bound variable, `k`,
could exceed the length of the array. To fix this, we put the standard bounds on `index`,
`0 <= index <= a.Length`. Note that because we say `k < index`, the
array access is still protected from error
even when `index == a.Length`. The use of a variable that
is one past the end of a growing range is a common pattern when working with
arrays, where it is often used to build a property up one element at a time.
The complete method is given below:

<!-- %check-verify -->
```dafny
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}
```

**Exercise 12.**
  *Write a method that takes an integer array, which it requires to
  have at least one element, and returns an index to the maximum of
  the array's elements. Annotate the method with pre- and
  postconditions that state the intent of the method, and annotate its
  body with loop invariant to verify it.*

<!-- %check-resolve -->
```dafny
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
{
  // Fill in the body that calculates the INDEX of the maximum.
}
```

A linear search is not very efficient, especially when many
queries are made of the same data. If the array is sorted, then we can use the
very efficient binary search procedure to find the key. But in order for us to
be able to prove our implementation correct, we need some way to require that
the input array actually is sorted. We could do this directly with a quantifier
inside a requires clause of our method, but a more modular way to express this
is through a *predicate*.

## Predicates

A predicate is a function which returns a boolean. It is a
simple but powerful idea that occurs throughout Dafny programs. For example, we
define the *`sorted`
predicate* over arrays of integers as a function that takes an array
as an argument, and returns `true` if and only if that array is
sorted in increasing order. The use of predicates makes our code shorter, as we
do not need to write out a long property over and over. It can also make our
code easier to read by giving a common property a name.

There are a number of ways we could write the `sorted`
predicate, but the easiest is to use a quantifier over the indices of the
array. We can write a quantifier that expresses the property, "if `x` is before
`y` in the array, then `x <= y`," as a quantifier over two bound variables:

<!-- %no-check -->
```dafny
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
```

Here we have two bound variables, `j`
and `k`, which are both integers. The comparisons between
the two guarantee that they are both valid indices into the array, and that
`j` is before `k`. Then the second part
says that they are ordered properly with respect to one another. Quantifiers are just
a type of boolean valued expression in Dafny, so we can write the sorted predicate
as:

<!-- %check-verify guide.20.expect -->
```dafny
predicate sorted(a: array<int>)
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
```

Note that there is no return type, because predicates always return a boolean.

Dafny rejects this code as given, claiming that the predicate
cannot read `a`. Fixing this issue requires
another annotation, the *reads annotation*.

## Framing

The sorted predicate is not able to access the array because
the array was not included in the function's *reading frame*. The
reading frame of a function (or predicate) is all the memory locations
that the function is allowed to read. The reason we might limit what a function
can read is so that when we write to memory, we can be sure that functions that
did not read that part of memory have the same value they did before. For
example, we might have two arrays, one of which we know is sorted. If we did
not put a reads annotation on the sorted predicate, then when we modify the
unsorted array, we cannot determine whether the other array stopped being
sorted. While we might be able to give invariants to preserve it in this case,
it gets even more complex when manipulating data structures. In this case,
framing is essential to making the verification process feasible.

<!-- %check-verify -->
```dafny
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
```

A `reads` annotation is not a boolean expression, like the
other annotations we have seen, and can appear anywhere along with the pre- and
postconditions. Instead of a property that should be true, it specifies a set
of memory locations that the function is allowed to access. The name of an
array, like `a` in the above example, stands for all the
elements of that array. One can also specify object fields and sets of objects,
but we will not concern ourselves with those topics here. Dafny will check that
you do not read any memory
location that is not stated in the reading frame. This means that function
calls within a function must have reading frames that are a subset of the
calling function's reading frame. One thing to note is that parameters to the
function that are not memory locations do not need to be declared.

Frames also affect methods. As you might have guessed, they
are not required to list the things they read, as we have written a method
which accesses an array with no `reads` annotation. Methods are allowed to read
whatever memory they like, but they are required to list which parts of memory
they modify, with a *modifies annotation*. They are almost identical
to their `reads` cousins,
except they say what can be changed, rather than what the value of the function
depends on. In combination with reads, modification
restrictions allow Dafny to prove properties of code that would otherwise be
very difficult or impossible. `reads` and `modifies` are among the tools that
enable Dafny to work on one method at a time, because they restrict what would
otherwise be arbitrary modifications of memory to something that Dafny can
reason about.


Note that framing only applies to the *heap*, or memory accessed through
references. Local variables are not stored on the heap, so they cannot be mentioned
in `reads` annotations. Note also that types like sets, sequences, and multisets are value
types, and are treated like integers or local variables. Arrays and objects are
reference types, and they are stored on the heap (though as always there is a subtle
distinction between the reference itself and the value it points to.)


**Exercise 13.**
  *Modify the definition of the `sorted` predicate so that it returns
  true exactly when the array is sorted and all its elements are
  distinct.*

<!-- %check-resolve -->
```dafny
predicate sorted(a: array<int>)
  reads a
{
  false // Fill in a new body here.
}
```

**Exercise 14.**
  *Change the definition of `sorted` so that it allows its argument to be 
  null (using a nullable array type) but
  returns false if it is.*

<!-- %check-verify -->
```dafny
predicate sorted(a: array<int>) // Change the type
  reads a
{
  // Change this definition to treat null arrays as "not sorted".
  // (i.e. return false for null arrays)
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
```

## Binary Search

Predicates are usually used to make other annotations clearer:

<!-- %check-resolve -->
```dafny
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  // This one is a little harder. What should go here?
}
```

We have the same postconditions that we did for the linear
search, as the goal is the same. The difference is that now we know the array
is sorted. Because Dafny can unwrap functions, inside the body of the method it
knows this too. We can then use that property to prove the correctness of the
search. The method body is given below:

<!-- %check-verify -->
```dafny
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
      0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
```

This is a fairly standard binary search implementation. First we
declare our range to search over. This can be
thought of as the remaining space where the key could possibly be. The range is
inclusive-exclusive, meaning it encompasses indices \[`low`, `high`). The first
invariant expresses the fact that this range is within the array. The second
says that the key is not anywhere outside of this range. In the first two
branches of the `if` chain, we find the element in the middle of our range is not
the key, and so we move the range to exclude that element and all the other
elements on the appropriate side of it. We need the addition of one when moving
the lower end of the range because it is inclusive on the low side. If we do not add one, then
the loop may continue forever when `mid == low`, which
happens when `low + 1 == high`. We could change this to
say that the loop exits when `low` and `high` are one apart, but this would mean we
would need an extra check after the loop to determine if the key was found at
the one remaining index. In the above formulation, this is unnecessary because
when `low == high`, the loop exits. But this means that
no elements are left in the search range, so the key was not found. This can be
deduced from the loop invariant:

<!-- %no-check -->
```dafny
  invariant forall i ::
    0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
```

When `low == high`, the negated
condition in the first part of the implication is always true (because no `i`
can be both at least and strictly smaller than the same
value). Thus the invariant says that all elements in the array are not the key,
and the second postcondition holds. As you can see, it is easy to introduce
subtle off by one errors in this code. With the invariants, not only can Dafny
prove the code correct, but we can understand the operation of the code more easily
ourselves.


**Exercise 15.**
  *Change the assignments in the body of `BinarySearch` to set `low`
  to `mid` or to set `high` to `mid - 1`. In each case, what goes
  wrong?*

<!-- %check-verify -->
```dafny
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
```

## Conclusion

We've seen a whirlwind tour of the major features of Dafny,
and used it for some interesting, if a little on the small side, examples of
what Dafny can do. But to really take advantage of the power Dafny offers, one
needs to plow ahead into the advanced topics: objects, sequences and sets, data
structures, lemmas, etc. Now that you are familiar with the basics of Dafny,
you can peruse the tutorials on each of these topics at your leisure. Each
tutorial is designed to be a relatively self-contained guide to its topic,
though some benefit from reading others beforehand. The examples are also a
good place to look for model Dafny programs. Finally, the reference contains the
gritty details of Dafny syntax and semantics, for when you just need to know
what the disjoint set operator is (it's `!!`, for those
interested).

Even if you do not use Dafny regularly, the idea of writing
down exactly what it is that the code does in a precise way, and using this to
prove code correct is a useful skill. Invariants, pre- and postconditions,
and annotations are useful in debugging code, and also as documentation for future
developers. When modifying or adding to a codebase, they confirm that the
guarantees of existing code are not broken. They also ensure that APIs are used
correctly, by formalizing behavior and requirements and enforcing correct
usage. Reasoning from invariants, considering pre- and postconditions, and
writing assertions to check assumptions are all general computer science skills
that will benefit you no matter what language you work in.
