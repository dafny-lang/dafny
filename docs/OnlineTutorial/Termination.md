<p></p> <!-- avoids duplicate title -->

# Termination

Dafny proves that all programs terminate. There are two
potential sources of non-terminating (divergent) behavior: loops and recursive
functions and methods. Dafny employs a single technique for handling either
case, *decreases annotations*.

A decreases annotation specifies a value, called the *termination measure*,
that becomes strictly smaller each time a loop is traversed or each time a
recursive function or method is called. This value is also bounded so that it
cannot decrease forever. This way, if the value starts at any arbitrary finite
value, the loop or recursion must stop. To prove this, Dafny proves that the
termination measure gets smaller on each iteration. If Dafny cannot prove this,
it says there is a failure to decrease termination measure. Because each kind
of termination measure comes with a built-in lower bound, this is all Dafny
needs to do to prove termination.

There are several kinds of values that Dafny can use in
decreases annotations, but the most common are integers. Integers have a
natural lower bound, zero, and it is usually quite easy to prove that they
decrease. Since many loops iterate through indices, these kinds of termination
proofs are very common. For example, we may have the following loop:

```dafny <!-- %check-verify -->
method m(n: nat)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    // do something interesting
     i := i + 1;
  }
}
```

If we give this to Dafny, we see that it verifies
immediately. But how did it know that this terminates? Because this is such a
common loop form, Dafny has a special rule for guessing the termination
measure. Dafny sees that there is no explicit decreases annotation, so it tries
to guess one. It sees that the loop condition is a comparison of the form `A < B`,
 for some `A` and `B`, so it makes the guess:

```dafny <!-- %no-check -->
  decreases B - A
```

in this case:

```dafny <!-- %no-check -->
  decreases n - i
```

If we add this annotation to the loop, it continues to
verify. Dafny is actually a little less strict than requiring the termination
measure to be bounded by zero. Really what it requires is that the loop does
not execute again when the termination measure is negative. So we could write:

```dafny <!-- %check-verify -->
method m()
{
  var i, n := 0, 11;
  while i < n
    decreases n - i
  {
    // do something interesting
    i := i + 5;
  }
}
```

Here, on the last iteration, `i`
becomes `15`, so the termination measure is `-4`. But here we have that the loop
guard is false, so the loop will not be executed again. Note we had to drop the
loop invariant, as `i` can now exceed `n`.

Dafny proves the termination of the whole program, not just
loops. To do this, it uses the same technique for recursive functions and methods.
Dafny analyzes which functions/methods call each other, to figure out possible
recursion. For each function/method that is possibly recursive, it requires
either an explicit or implicit decreases annotation on the function or method.
Most recursive functions/methods are self-recursive:

```dafny <!-- %check-verify -->
function fac(n: nat): nat
{
  if n == 0 then 1 else n * fac(n-1)
}
```

Dafny accepts this program as is. It turns out that for most
functions which are recursive, they just call themselves with smaller values of
the parameters, so the parameters decreasing is the default guess. The
decreases annotation can be made explicit by adding:

```dafny <!-- %no-check -->
  decreases n
```

to the function declaration.

Sometimes it is beneficial to have loops which may not
terminate, or where a proof of termination is unknown. For example, consider
the following method:

```dafny <!-- %check-verify -->
method hail(N: nat)
  decreases *
{
  var n := N;
  while 1 < n
    decreases *
  {
    n := if n % 2 == 0 then n / 2 else n * 3 + 1;
  }
}
```


This program terminates if and only if the Collatz
conjecture is true, which is an open problem in mathematics, so you can't really
expect Dafny to be able to prove termination. You could also code something like a
stream processor, which is intended to run forever. Thus Dafny provides an
"out," a special annotation that instructs Dafny not to attempt to prove
termination, which is given above in the `hail` method. This can be used
on all non-ghost loops. Note that a method containing a loop marked with
`decreases *` must itself be marked with `decreases *`.

Dafny can use values other than integers as termination
measures. When a sequence is specified, Dafny automatically uses the length as
a termination measure. Sets are considered smaller if one is a strict subset of
the other, so each set must be contained in the previous. With sets, the empty
set is as small as you can go, and sequences have natural number lengths, so
both of these come with lower bounds. Though not terribly useful, bools and
references can also be used in decreases clauses. (See the reference if you
want details.) The final kind of termination measure is a tuple of the other kinds of
measures. For example, the following implementation of the Ackermann function
uses a pair of integers to prove termination:

```dafny <!-- %check-verify -->
function Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then n + 1
  else if n == 0 then Ack(m - 1, 1)
  else Ack(m - 1, Ack(m, n - 1))
}
```

Here the decreases clause is explicitly written out, even
though Dafny will guess the exact same thing. A tuple uses the size comparisons
of the component values to determine whether the measure has shrunk. In this
case it uses two integers, but in general the different parts can be of
different categories. The comparison works *lexicographically*.
If the first element, in this case m, is smaller, than it doesn't matter what
happens to the other values. They could increase, decrease, or stay the same.
The second element is only considered if the first element doesn't change.
If the first element does not change, the second value needs to decrease. If neither the first or second changes, then the third element
must decrease, etc. Eventually, one of the elements must decrease. Past that
point, any further elements are again free to increase or do whatever they
like.

In the `Ack`
function, there are three recursive calls. In the first, `m` becomes one
smaller, but `n` increases. This is fine because `n` comes after `m`
in the tuple. In the second call, `m` decreases as well, so the second argument
is allowed to be any value (which is good, because Dafny doesn't really prove
anything about the result of the third recursive call). Dafny does need to prove that
the third call obeys the termination measure. For this call, `m` remains the same,
but `n` decreases, so the overall measure decreases as well.

Termination applies not just to single functions/methods,
but also to multiple mutually recursive functions/methods. For example,
consider this pair of recursively defined parity predicates:

```dafny <!-- %check-verify -->
predicate even(n: nat)
  ensures even(n) <==> n % 2 == 0
{
  if n == 0 then true else odd(n-1)
}
predicate odd(n: nat)
  ensures odd(n) <==> n % 2 != 0
{
  if n == 0 then false else even(n-1)
}
```

Dafny proves that they terminate by considering all possible
paths through the two functions.
