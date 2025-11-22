// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/// # Fixpoint combinators with provable termination guarantees
///
/// *Mikael Mayer*, 2022/09/22
///
/// Fixpoints are functions combinators such that, if they exist,
/// then we don't need to define recursion or mutual recursion at all,
/// only use fixpoints when we need recursion.
/// Let's start by illustrating an example

module {:options "-functionSyntax:4"} Fixpoints {

/// We first define the usual Fibonacci function
/// To make Dafny happy, we need to provide a (normally implicit) decreases clause,
/// and Dafny will verify that 0 <= n-1 < n and 0 <= n-2 < n when n > 2

  function Fib1(n: nat): nat
    decreases n
  {
    if n <= 1 then n else Fib1(n-1) + Fib1(n-2)
  }

/// This is nice, but mathematically speaking, we are still defining a function in terms of itself,
/// which is not obvious.
/// Besides a while loop and a stack to implement recursive functions,
/// there is also another way , using fixpoint combinators.
///
/// A fixpoint combinator typically takes a 'template function' that, if provided with the final function and an input,
/// execute the body of the function we want where they replace recursive calls with the provided final functions.
/// We can write a fibonacci function using a combinator like this:

  function Fib2(n: nat): nat {
    var comb :=
      (f: nat -> nat, n': nat) => if n' <= 1 then n' as nat else f(n'-1) + f(n'-2);
    fixpoint2(comb, n)
  }

/// The signature of this fixpoint combinator could typically be:

  function fixpoint2(comb: (nat -> nat, nat) -> nat, u: nat): nat

/// However, any attempt at writing the body of fixpoint will fail, because Dafny will always check for
/// termination.
  {
    var callback := (u': nat) => fixpoint2(comb, u');
    comb(callback, u)
  }

/// So let's fix that. Fix, we need to realize that, in order for fixpoint to finish, we need to
/// that u' is less than u. But doing so changes the type of the first argument of comb from nat -> nat
/// to nat --> nat (see [arrow subset types](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-arrow-subset-types))
/// Let's do the change

  function fixpoint3(comb: (nat --> nat, nat) -> nat, u: nat): nat
    decreases u
  {
    var callback := (u': nat) requires u' < u => fixpoint3(comb, u');
    comb(callback, u)
  }

/// Everything looks great, but when it comes to defining our fibonacci function, things fail
/// It says our `comb` function does not satisfy the subset constraints
/// This is because `comb` is only taking `nat -> nat` as first argument, a total function,
/// whereas it should now accept more general functions that can have preconditions
/// that can have requirements.

  function Fib3(n: nat): nat {
    var comb :=
      (f: nat -> nat, n: nat) => if n <= 1 then 1 as nat else f(n-1) + f(n-2);
    fixpoint3(comb, n)
  }

/// So let's do the signature transformation and have the first argument of `comb` to be `f: nat --> nat`.
/// Now, Dafny complains that `f` might not be applicable
/// to n-1 or n-2, which we expected.
/// We need to say something about that. We thus add a `requires` clause to the lambda
/// Let's take our best guess and require that `f` can be applied for every number below `n`.

  function Fib4(n: nat): nat {
    var comb :=
      (f: nat --> nat, n: nat) requires forall n': nat | n' < n :: f.requires(n') =>
        if n <= 1 then 1 as nat else f(n-1) + f(n-2);
    fixpoint3(comb, n)
  }

/// Now the error is on `comb` as an argument, because the type of `comb` in `fixpoint3` should be
/// `(nat --> nat, nat) -> nat`, which is a total function
/// We need to change it to a partial function as well:

  function fixpoint5(comb: (nat --> nat, nat) --> nat, u: nat): nat
    decreases u
  {
    var callback := (u': nat) requires u' < u => fixpoint5(comb, u');
    comb(callback, u)
  }

/// Now, we one error. We don't know if `comb` can be applied on `callback` and `u`.
/// What is needed for that?
/// We need to prove that `comb.requires(callback, u)`
/// but it's not general enough to put it as a `requires` clause. If we try, we get another error

  function fixpoint6(comb: (nat --> nat, nat) --> nat, u: nat): nat
    decreases u
    requires var callback := (u': nat) requires u' < u => fixpoint6(comb, u');
             comb.requires(callback, u)
  {
    var callback := (u': nat) requires u' < u => fixpoint6(comb, u');
    comb(callback, u)
  }

/// Dafny will not be able to prove this precondition for the recursive call !
/// Maybe we can abstract away the callback and just try to prove that any callback should make it?

  function fixpoint7(comb: (nat --> nat, nat) --> nat, u: nat): nat
    decreases u
    requires forall callback: nat --> nat ::
               comb.requires(callback, u)
  {
    var callback := (u': nat) requires u' < u => fixpoint7(comb, u');
    comb(callback, u)
  }

/// Uh oh, our forall is still missing something there. We asked `comb` to work with any `callback`
/// for the given `u`.
/// But now, the recursive call to fixpoint6 requires that `comb` work with any `callback` for the given `u'`.
/// Maybe our requirement was too weak. What to put in the requires so that it works nicely?
/// You could try a lot of combinations there and quickly get lost.
///
/// Let's go back to our origina fibonacci function:

  function Fib7(n: nat): nat {
    var comb :=
      (f: nat --> nat, n: nat) requires forall n': nat | n' < n :: f.requires(n') =>
        if n <= 1 then 1 as nat else f(n-1) + f(n-2);
    fixpoint7(comb, n)
  }

/// Here, what is the strongest requirement we can provide to fixpoint7
/// Easy: It's in the signature of `comb`. We can write our guess below the definition of our `comb`,
/// as an assertion that Dafny is able to prove.

  function Fib8(n: nat): nat {
    var comb :=
      (f: nat --> nat, n: nat) requires forall n': nat | n' < n :: f.requires(n') =>
        if n <= 1 then 1 as nat else f(n-1) + f(n-2);
    assert forall f: nat --> nat, n: nat | (forall n': nat | n' < n :: f.requires(n')) ::
        comb.requires(f, n);
    fixpoint7(comb, n)
  }

/// This is the strongest postcondition we can obtain to determine when we can prove that `comb.requires(f, n)`
/// So it has to be sufficient for our fixpoint. let's give it a try and enter it in the fixpoint:

  function fixpoint9(comb: (nat --> nat, nat) --> nat, u: nat): nat
    decreases u
    requires forall f: nat --> nat, n: nat | (forall n': nat | n' < n :: f.requires(n')) ::
               comb.requires(f, n);
  {
    var callback := (u': nat) requires u' < u => fixpoint9(comb, u');
    comb(callback, u)
  }

/// Suddenly, everything works! how is that possible?
/// More suprisingly, how can it even prove that `comb.requires(callback, u)` holds?
/// The precondition does not mention `u` anymore. And that's ok! We did not want the precondition
/// to depend on the initial value, after all.
/// To answer our last question, to prove `comb.requires(callback, u)` holds,
/// Dafny has no choice but instantiate the requires,
/// and needs to prove that `forall n': nat | n' < n :: callback.requires(n')`
/// But this is exactly what the definition of `callback` gives us!
/// And so ends our adventure... or does it?
/// 
/// Oh, we just need to change the return type of the `comb` function
/// Dafny wrongly infers it as an `int`, so we use a trick of assigning it to a variable
/// `x` of type `nat` so that the return type is checked to be nat:

  function Fib9(n: nat): nat {
    var comb :=
      (f: nat --> nat, n: nat) requires forall n': nat | n' < n :: f.requires(n') =>
        var x: nat := if n <= 1 then 1 else f(n-1) + f(n-2); x;
    fixpoint9(comb, n)
  }

/// Let's recap what you just learned:
///
/// - A partial function `f` can be applied on `A` only if Dafny can prove that `f.requires(A)`
/// - To prove that `f.requires(A)` at a call site, we either need to prove the actual precondition itself,
///   or if `f` was passed as a parameter, we need a precondition on how we can prove `f.requires(A)`
/// - Instead of looking for the weakest precondition for a function, and strengthening it,
///   you can borrow the strongest condition that you have at a call site.
///
/// # Exercises and solutions
/// 
/// 1. Generalize fixpoint to any input and output type
/// 2. Generalize fixpoint to support mutually recursive functions*
///
/// Solution to exercise 1:

  function Fib(n: nat): nat {
    var comb :=
      (f: nat --> nat, n: nat) requires forall n': nat | n' < n :: f.requires(n')
      => var x: nat := if n <= 1 then 1 else f(n-1) + f(n-2); x;
    TerminatingFixpoint<nat, nat>(i => i, comb, n)
  }

  function TerminatingFixpoint<U(!new), V(!new)>(
    ghost decreaseMeasure: U -> nat,
    comb: (U --> V, U) --> V, init: U
  ): (v: V)
    decreases decreaseMeasure(init)
    requires
      forall callback: U --> V, u: U |
        (forall u': U | decreaseMeasure(u') < decreaseMeasure(u) :: callback.requires(u'))
      :: comb.requires(callback, u)
  {
    var callback :=
      (u: U) requires decreaseMeasure(u) < decreaseMeasure(init) =>
        TerminatingFixpoint(decreaseMeasure, comb, u);
    comb(callback, init)
  }

/// Solution to exercise 2: Mutually recursive functions

  function even(n: nat): bool {
    var functions := {"even", "odd"};
    var comb :=
      map[
        "even" := (f: (string, nat) --> bool, n: nat) requires forall n': nat, s <- functions | n' < n :: f.requires(s, n')
          => if n == 0 then true else !f("odd", n-1),
        "odd" := (f: (string, nat) --> bool, n: nat) requires forall n': nat, s <- functions | n' < n :: f.requires(s, n')
          => if n == 0 then false else !f("even", n-1)
      ];
    TerminatingMultipleFixPoint<nat, bool>(functions, i => i, comb, "even", n)
  }

  function TerminatingMultipleFixPoint<U(!new), V(!new)>(
    ghost functions: set<string>,
    ghost decreaseMeasure: U -> nat,
    comb: map<string, ((string, U) --> V, U) --> V>,
    fun: string,
    init: U
  ): (v: V)
    requires comb.Keys == functions
    requires fun in functions
    decreases decreaseMeasure(init)
    requires
      forall callback: (string, U) --> V, fun: string, u: U |
        fun in functions &&
        (forall fun': string, u': U | fun' in functions && decreaseMeasure(u') < decreaseMeasure(u) :: callback.requires(fun', u'))
      :: comb[fun].requires(callback, u)
  {
    var callback :=
      (f: string, u: U) requires f in functions && decreaseMeasure(u) < decreaseMeasure(init) =>
        TerminatingMultipleFixPoint(functions, decreaseMeasure, comb, f, u);
    comb[fun](callback, init)
  }
}
