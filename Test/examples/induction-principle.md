date: 2022-08-25
author: @sonmarcho

# Defining and using an induction principle in Dafny

This note explores a way of factorizing proofs when writing a collection of lemmas about a
single function, by means of an *induction principle*. This proof technique turned out
to be particularly useful when working on
[Dafny-in-Dafny](https://github.com/dafny-lang/compiler-bootstrap),
which we will use as a motivating example. The full code development can be found in the
[`induction-principle`](induction-principle/) folder. The development with the preserved git
history can be found in the [Dafny github project](https://github.com/dafny-lang//dafny) and the source code itself is [here](./induction-principle).

## Problem: proving lemmas about an interpreter

In the context of verifying a compiler, we need to introduce a semantics for the compiled
language. We can do so by defining a function `InterpExpr(e: Expr, st: State):
Result<(Value, State), Error>`, which given an expression and an initial state either
returns an error (division by zero, access to an unbound variable, etc.) or returns the
value this expression evaluates to, together with the new state in which the execution
terminates.

Verifying the compiler then requires us to repeatedly state and prove lemmas about this
`InterpExpr` function. For instance, given a transformation `TR: (Expr) -> Expr`, we might
express the correctness of the transformation in the following way (which says that the new program fails no more often than
the original one, and evaluates to the same result):

```dafny
forall e, st :: InterpExpr(e, st).Success? ==> InterpExpr(e, st) == InterpExpr(TR(e), st)
```

Such a lemma has to be proved over `e` or over the execution of the interpreter (that is, only some
lemmas can be proved by induction over `e`) for all the transformations we wish to
verify, and its proof generally follows very closely the structure of `InterpExpr`. This is
for instance the case for the following local rewriting:

```dafny
0 * e  -->  0       when e is pure
```

Moreover, verifying this rewriting requires us to prove the following auxiliary lemma (for the appropriate
definition of `IsPure`) which, again, mentions `InterpExpr`:

```dafny
forall e, st ::
  IsPure(e) ==>
    match InterpExpr(e, st)
      case Success((_, st')) => st' == st // state is unchanged
      case Failure => true
```

**Note:** We mention above that not all lemmas can be proved by induction over the syntax.
It is for instance the case if the AST contains loops, in which situation we often need to
manipulate a notion of fuel when defining the interpreter: the lemmas then require doing
the induction also on the fuel. Let's assume we can always do the induction on the syntax only
(and in particular that there are no loops).

The issue we encounter here is that we have a lot of lemmas to prove about a single
function, `InterpExpr`. However, whenever we need to prove such a lemma in Dafny, we need
more or less to copy/paste the whole `InterpExpr` definition because the structure of the
proof follows the structure of this function. This process is time consuming,
leads to big proofs which are hard to maintain, and is error prone as we are blind while
instantiating function calls and lemmas calls (in particular, it is very easy to mix up
variable indices).

For instance, let's look at the correctness proof for the ``IsPure`` predicate, that we introduce
below:

```dafny
predicate method IsPure(e: Expr, locals: set<string> := {})
  decreases e
  // `locals`: the set of local variables which have been introduced by outer
  // let-bindings (if the expression only updates those variables then it is
  // pure, because those variables don't escape the scope of the term).
{
  match e
    case Var(name) => true
    case Literal(n) => true
    case Bind(bvar, bval, body) =>
      && IsPure(bval, locals)
      && IsPure(body, {bvar} + locals)
    case Assign(avar, aval) =>
      avar in locals && IsPure(aval, locals)
    case If(cond, thn, els) =>
      && IsPure(cond, locals)
      && IsPure(thn, locals)
      && IsPure(els, locals)
    case Op(op, oe1, oe2) =>
      IsPure(oe1, locals) && IsPure(oe2, locals)
    case Seq(e1, e2) =>
      IsPure(e1, locals) && IsPure(e2, locals)
}
```

We want to prove the following theorem:

<a id="interpexpr-pure"></a>
```dafny
lemma InterpExpr_Pure(e: Expr, ctx: Context)
  requires Pure.IsPure(e)
  ensures
    match InterpExpr(e, ctx)
      case Success((_, ctx')) => ctx' == ctx // state is unchanged
      case Failure => true
```

where a context is a map from strings to values:
```dafny
type Context = map<string, int>
```

This theorem can be deduced from the following intermediate lemma, that we prove by
induction on the expression `e`:

```dafny
lemma InterpExpr_Pure(e: Expr, locals: set<string>, ctx: Context)
  requires IsPure(e, locals)
  requires ctx.Keys >= locals
  ensures
    match InterpExpr(e, ctx)
      case Success((_, ctx')) =>
        && ctx'.Keys == ctx.Keys
        // We only update variables captured by outer let-bindings
        && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
      case Failure => true
```

Let's consider the `Seq` case. In our AST, we define sequences as follows:

```dafny
datatype Expr =
  | Seq(e1: Expr, e2: Expr)
  | ... // Omitted
```

And the interpreter is defined on sequences as follows:

```dafny
function method InterpExpr(e: Expr, ctx: Context): Result<(int, Context)> {
  match e
    case Seq(e1, e2) =>
      var (_, ctx1) :- InterpExpr(e1, ctx); // Evaluate the first expression
      InterpExpr(e2, ctx1) // Continue

    // Omitted
    case ... =>
      ...
}
```

We face the problem that the proof of the `Seq` case requires introducing the same
intermediate values as the ones manipulated by the interpreter (like `ctx1`), so that we
can *write* the recursive calls to `InterpExpr_Pure` (which give us our
induction hypotheses):

```dafny
lemma InterpExpr_Pure ... {
  match e
    case Seq(e1, e2) =>
      var res1 := InterpExpr(e1, ctx); // Duplicates the interpreter
      InterpExpr_Pure(e1, locals, ctx); // *Recursive call*

      if res1.Success? { // Not even in the interpreter (subsumed by the assignment with `:-`)!
        var (_, ctx1) := res1.value; // Duplicates the interpreter
        InterpExpr_Pure(e2, locals, ctx1); // *Recursive call*
      }
      else {} // Trivial case

    case ... =>
      ...
}
```

As a result, the proof above basically duplicates the code of the interpreter. This is
true for all the cases of `Expr`, and has to be done for all the lemmas we prove about the
interpreter, leading to obvious scalability issues.

**Note:** The full proof without the induction principle is defined in the [`PureNoInductionPrinciple`](induction-principle/PureNoInductionPrinciple.dfy)
module. It is particularly interesting in the context of incrementally expanding the language,
to compare the effort needed to update the proofs, depending on whether those proofs use
the induction principle or not (see the [corresponding section](#section-increments)).

## Our solution: defining an induction principle

### First version of the induction principle - verifying `Pure`

If you look carefully at the proof of `InterpExpr_Pure` in the previous
section, you will notice that the only important lines of code are the recursive calls
applied on `e1` and `e2`. The remaining lines simply introduce variables like `ctx1` so
that we can actually *write* those calls. We might want to factor out this structure once
and for all.

Let's introduce a predicate for the property we want to prove:

<a id="p-predicate"></a>
```dafny
predicate P(locals: set<string>, ctx: Context, e: Expr)
{
  // The precondition of ``InterpExpr_Pure``:
  IsPure(e, locals) ==>
  ctx.Keys >= locals ==>
  // The postcondition of ``InterpExpr_Pure``:
  match InterpExpr(e, ctx)
    case Success((_, ctx')) =>
      && ctx'.Keys == ctx.Keys
      && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
    case Failure => true
}
```

We can then isolate the proof step we do for the `Seq` case in the following lemma:

<a id="ind-step-seq-forall"></a>
```dafny
lemma InterpExpr_Pure_Seq(e1: Expr, e2: Expr)
  requires forall locals, ctx :: P(locals, ctx, e1) // Induction hyp. for e1
  requires forall locals, ctx :: P(locals, ctx, e2) // Induction hyp. for e2
  ensures forall locals, ctx :: P(locals, ctx, Seq(e1, e2)) // Goal
```

An interesting thing with the above lemma is that its proof goes through automatically!

We can write similar lemmas for the other cases of `Expr`, and finally make the final
proof by induction in the following manner:

```dafny
lemma InterpExpr_Pure(e: Expr)
  ensures forall locals, ctx :: P(locals, ctx, e)
{
  match e
    case Seq(e1, e2) =>
      // Induction hypothesis for `e1`
      InterpExpr_Pure(e1);

      // Induction hypothesis for `e2`
      InterpExpr_Pure(e2);

      // Proof of the induction step for `Seq`
      InterpExpr_Pure_Seq(e1, e2);

    // Omitted
    case ... =>
      ...
}
```

The interesting thing to notice now is that the proof we just sketched above should be the
same whatever the property we wish to prove about the interpreter. In the present case,
the proof of [the induction step for `Seq`](#ind-step-seq-forall) goes through automatically.
The proof for other properties `P` might need a bit more work, but the induction
step is the same: to prove `P` by induction on the expression, in the `Seq` case,
we need the assumption that `P` is true on the elements of the sequence.

As a consequence, we can package the proof above in an abstract module, to be able
to reuse it for other properties:

```dafny
abstract module Induction {
  // State type
  type S

  // The property we wish to prove
  predicate P(st: S, e: Expr)

  // The lemmas for the various cases of the induction step - must be proven
  // for the various instantiations of the induction principle
  lemma Induct_Seq(e1: Expr, e2: Expr)
    requires forall st :: P(st, e1)
    requires forall st :: P(st, e2)
    ensures forall st :: P(st, Seq(e1, e2))

  ... // Other cases: omitted

  // The inductive proof, performed once and for all
  lemma Induct(e: Expr)
  ensures forall st :: P(st, e)
  {
    match e
      case Seq(e1, e2) =>
        Induct(e1); // Recursion
        Induct(e2); // Recursion
        Induct_Seq(e1, e2); // Induction step for `Seq`

      // Other cases: omitted
      case ... =>
        ...
  }
```

In the case of `InterpExpr_Pure`, we would instantiate the `Induction` module in
the following manner:

```dafny
module Pure refines Induction {
  // The state contains the context, of course, but also the set of local variables
  // found in the outer bindings.
  type S = State(locals: set<string>, ctx: Context)

  // Put aside the fact that we use a state of type ``S``, this is the same predicate as ``P`` above
  predicate P ... {
    var (locals, ctx) := st;
    IsPure(e, locals) ==>
    ctx.Keys >= locals ==>
    match InterpExpr(e, ctx)
      case Success((_, ctx')) =>
        && ctx'.Keys == ctx.Keys
        && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
      case Failure => true
  }

  lemma Induct_Seq ... {} // Goes through automatically!

  ... // Other cases: omitted

  // And we get the theorem for all `e` for free!
}
```

### Refined induction principle - verifying `Pure`

Stating an induction principle the way we did above enables factorizing a lot of work,
but there are still some issues. First, the proof of `Induct_Seq` goes through
automatically in this case, but other cases of the AST and other lemmas may need a bit
of manual work, for instance by calling intermediate lemmas. In order to do so, we
might need to access the different values manipulated by the interpreter (the intermediate
context `ctx1` for instance). Moreover, it uses forall quantifiers: the instantiation of
those quantifiers can be unpredictable, and worse, can lead to context explosions when
the proofs become more complex. For those reasons, we might want to be a bit more precise.

The refinement we suggest (shown in the [code development](induction-principle/Pure.dfy)) works as follows. In order to
manipulate the intermediate states, we need to talk about execution success and
failures. Going back to the specific proof of
[`InterpExpr_Pure`](#interpexpr-pure), we split the
[`P`](#p-predicate) predicate as follows:

```dafny
predicate P_Succ(locals: set<string>, ctx: Context, e: Expr, ctx': Context, v: int)
  // Success: the preconditions are true and we successfully evaluate `e` to
  // a pair (value, new state)
{
  && IsPure(e, locals)
  && ctx.Keys >= locals
  && InterpExpr(e, ctx) == Success((v, ctx'))
  && ctx'.Keys == ctx.Keys
  && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
}

predicate P_Fail(locals: set<string>, ctx: Context, e: Expr)
  // Failure: the preconditions are false or we fail to evaluate `e`
{
  IsPure(e, locals) ==>
  ctx.Keys >= locals ==>
  InterpExpr(e, ctx).Failure?
}
```

`P_Succ` and `P_Fail` must satisfy the following important property:

```dafny
lemma P_ExcludedMiddle(locals: set<string>, ctx: Context, e: Expr)
  ensures P(locals, ctx, e) <==> P_Fail(locals, ctx, e) || exists ctx', v :: P_Succ(locals, ctx, e, ctx', v)
```

<br>

**Note:** In the generic induction principle, we actually don't request the property `P_ExcludedMiddle`
stated as above, but rather ask for the following function and lemmas. The reason is that
SMT solvers can have unpredictable performance on resolving existential quantifiers.
```dafny
    // Perform a single step of execution provided the execution doesn't fail
    function P_Step(st: S, e: Expr): (res: (S, V))
      requires P(st, e)
      requires !P_Fail(st, e)
      ensures P_Succ(st, e, res.0, res.1)

    lemma P_Fail_Sound(st: S, e: Expr)
      requires P_Fail(st, e)
      ensures P(st, e)

    lemma P_Succ_Sound(st: S, e: Expr, st': S, v: V)
      requires P_Succ(st, e, st', v)
      ensures P(st, e)
```

<br>

We can then split the ``InterpExpr_Pure_Seq`` lemma into several cases:

```dafny
// Case 1: evaluating the first element in the sequence fails
lemma InterpExpr_Pure_Seq_Fail(locals: set<string>, ctx: Context, e1: Expr, e2: Expr)
  requires P_Fail(locals, ctx, e1)
  ensures P(locals, ctx, Seq(e1, e2))

// Case 2: evaluating the first element in the sequence succeeds
lemma InterpExpr_Pure_Seq_Succ(
  locals: set<string>, ctx: Context, e1: Expr, e2: Expr,
  ctx1: Context, v: int)
  requires P_Succ(locals, ctx, e1, ctx1, v) // `e1` evaluates to `v` in `ctx1`
  requires P(locals, ctx1, e2) // The property is true for `e2` starting in `ctx1`
  ensures P(locals, ctx, Seq(e1, e2))
```

This way, the two cases (we fail when evaluating `e1` or not) are decomposed into small
lemmas. Moreover, when proving the result in the 2nd case (the most difficult one in
practice), we can directly reference the `ctx1` variable which is introduced as input to
the lemma.

Finally, the inductive proof of `InterpExpr_Pure` requires making a case
disjunction on whether we have `P_Fail(locals, ctx, e1)` or `P_Succ(locals, ctx, e1, ctx1,
v)` for some `ctx1` and `v` (the generic proof, performed for all `P`, is available
in [`Induction`](induction-principle/Induction.dfy)).

We invite the reader to have a look at the [code development](induction-principle/Pure.dfy). In practice, proving the
correctness of `IsPure` simply required correctly instantiating the various definitions
requested by the induction principle (i.e., `P`): all the proofs go through automatically.
Writing those definitions takes some lines of code, but is very straightforward. Moreover,
updating the proofs is a lot easier when using the induction principle (see
[`Incrementally expanding the language`](#section-increments)).

## Proofs by induction in an interactive theorem prover (with tactics)

An interesting thing to note is that we have to make our induction principle more precise
than what an interactive theorem prover like Coq would give us. The main reasons we do so
are that we want to consider all the cases in isolation to make them more tractable, and
we want not to rely on forall quantifiers, because they are hard to work with and make the
context saturate. More specifically, an interactive prover like Coq would more or less give
us the [first, unrefined induction principle](#ind-step-seq-forall) we introduced earlier.

More specifically, when trying to prove ``InterpExpr_Pure``, we would start
with the goal:

```Coq
GOAL 1:

  ======================================================
  forall (e: Expr) (locals: set<string>) (ctx: Context).
  IsPure(e, locals) ==>
  ctx.Keys >= locals ==>
  match InterpExpr(e, ctx)
    case Success((_, ctx')) =>
      && ctx'.Keys == ctx.Keys
      && forall x | x in ctx.Keys && x !in locals :: ctx'[x] == ctx[x]
    case Failure => true
```

Let's use the [`P`](#p-predicate) predicate for the purpose of clarity. This goal is equivalent to:
```Coq
GOAL 1:

  ========================================================================
  forall (e: Expr) (locals: set<string>) (ctx: Context). P(locals, ctx, e)
  
```

We introduce `e`:
```Coq
GOAL 2:
  e : Expr
  ========================================================================
  forall (locals: set<string>) (ctx: Context), P(locals, ctx, e)
```

We perform an induction on `e`. For the `Seq` case we get the following goal, which is exactly the first version
of our [induction theorem for `Seq`](#ind-step-seq-forall):

```Coq
GOAL 3:
  e1 : Expr
  e2 : Expr
  H1: forall (locals: set<string>) (ctx: Context). P(locals, ctx, e1)
  H2: forall (locals: set<string>) (ctx: Context). P(locals, ctx, e2)
  ========================================================================
  forall (locals: set<string>) (ctx: Context), P(locals, ctx, Seq(e1, e2))
```

## Verifying the transformation `0 * e ---> 0` (`EliminateMulZero`)

We set off on verifying a transformation which applies the following local rewritings:

```
0 * e ---> 0
e * 0 ---> 0
  when e is pure
```

The transformation is written by doing a recursive traversal of the AST, and applying the above
rewritings in a bottom-up manner. The interesting case is for
`Op(op: BinOp, oe1: Expr, oe2: Expr)` where `BinOp = | Add | Sub | Mul`. We first apply the
rewritings in the subexpressions `oe1` and `oe2` (we do a bottom-up transformation), then check if
the resulting expression can be simplified (the full function can be found in the [code development](induction-principle/EliminateMulZero.dfy)):

```dafny
function method Eliminate(e: Expr): Expr
  decreases e, 1
{
  match e
    case Op(op, oe1, oe2) =>
      var oe1' := Eliminate(oe1);
      var oe2' := Eliminate(oe2);
      if op.Mul? && (IsZeroMulPure(oe1', oe2') || IsZeroMulPure(oe2', oe1')) then
        Literal(0)
      else
        Op(op, oe1', oe2')

    // Other cases omitted
    case ... =>
      ...
}

predicate method IsZeroMulPure(e1: Expr, e2: Expr)
{
  && e1 == ZeroExpr
  && Pure.IsPure(e2)
}
```

As expected, only the `Op` case of the induction principle requires manual work, by calling
the lemma [`Pure.InterpExpr_Pure`](#interpexpr-pure) that we proved above, which states that
evaluating an expression which satisfies the `IsPure` predicate leaves the state unchanged.

## Verifying `VarUnchanged`

We also applied the induction principle to the proof that if an expression syntactically
doesn't update a free variable (i.e., not bound by a `let`), then this variable is not
updated during the evaluation.

We define a predicate `VarUnchanged(x: string, e: Expr)`, which returns `true` if the variable
`x` is not updated in expression `e`, while ignoring the places where it is shadowed by a let-binding.
The interesting cases are `Bind(bvar: string, bval: Expr, body: Expr)` and
`Assign(avar: string, aval: Expr)`.

```dafny
predicate method VarUnchanged(x: string, e: Expr)
  // Returns true if no assignments of `x` (not shadowed by a let-binding) appears
  // in `e`.
{
  match e
    case Bind(bvar, bval, body) =>
      // The rhs doesn't update x
      VarUnchanged(x, bval) &&
      // If the binding doesn't shadow x, the body of the let-binding doesn't update x
      (bvar == x || VarUnchanged(x, body))

    case Assign(avar, aval) =>
      // The variable we update is not x
      avar != x
      // And we don't update x in the rhs
      && VarUnchanged(x, aval)

    // Other cases omitted
    case ... =>
      ...
}

```

The property we want to prove is the following one:
```dafny
forall x, ctx, e ::
  VarUnchanged(x, e) ==>
  x in ctx ==>
  match InterpExpr(e, st.ctx)
    case Success((_, ctx')) =>
      && x in ctx'.Keys // x is also in the new environment
      && ctx'[x] == ctx[x] // x maps to the same value as before
    case Failure =>
      true
  Pre(st, e) ==> ResultSameX(st, res)
```

Because of the potential shadowing appearing in the `Bind` case, we actually can't use this
property directly in the inductive proof. We actually have to make the `x` string optional
(see the [code development](induction-principle/VarUnchanged.dfy) for the full details). Once this detail is properly handled, all the
proofs go through automatically.


<a id="section-increments"></a>

## Incrementally expanding the language

We now study how incremental updates to the AST impact the induction
principle and the proofs we have done so far.

<a id="section-increments-seq"></a>

### A more general version of `Seq`: `Seq(expr, expr) ---> Seq(seq<Expr>)`

The first modification we do is to transform the `Seq` case from `Seq(e1: Expr, e2: Expr)`
to `Seq(seq<Expr>)`. This requires adding a function to interpret sequences of expressions.
Anticipating a bit on the next language extension we will implement allowing assignments
and let-bindings to update/declare a sequence of variables -
see [next section](#section-increments-varseq); we define this function so that it returns
the *sequence* of the values the individual expressions evaluate to, rather than the value
the *last* expression in the sequence evaluates to:

```dafny
function method InterpExprs(es: seq<Expr>, ctx: Context): (r:Result<(seq<int>, Context)>)
  ensures r.Success? ==> |r.value.0| == |es|
  decreases es, 0
{
  if es == [] then Success(([], ctx))
  else
    var (v, ctx1) :- InterpExpr(es[0], ctx);      // Evaluate the first expression of the sequence
    var (vs, ctx2) :- InterpExprs(es[1..], ctx1); // Evaluate the rest of the sequence
    Success(([v] + vs, ctx2))
}
```

### Updating the induction principle
Because of this new `InterpExprs` function, we need to add new predicates to the induction principles.
We previously introduced `P`, `P_Succ` and `P_Fail` to state properties about `InterpExpr`,
we now need to introduce `Pes`, `Pes_Succ` and `Pes_Fail`, to state properties about `InterpExprs`.
Similarly to the `P` predicates which manipulate values of type `V`, the `Pes` predicates
manipulate sequences of values of type `VS`.

**Note:** If you wonder why we parameterize the induction principle by `V` and `VS`,
see this [section](#pair-of-state).

```dafny
predicate Pes(st: S, es: seq<Expr>)
predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS) // Success
predicate Pes_Fail(st: S, es: seq<Expr>) // Failure
```

Of course, we also request theorems similar to `P_Succ_Sound` and `P_Fail_Sound` for the `Pes`
predicates (not shown here).

Finally, because `VS` is not a concrete type, we need some constants and lemmas to be provided
by the user.
```dafny
function AppendValue(v: V, vs: VS): VS // Returns: [v] + vs

ghost const NilVS: VS // Empty sequence of values

function VS_Last(vs: VS): V // Last element of a non-empty sequence of values
  requires vs != NilVS
```

The induction lemmas for the `Seq` case are straightforward to update: the only important
thing is that they now sometimes use the `Pes` predicates instead of the `P` predicates
(we don't show those lemmas here).

The last elements we need to add are induction lemmas for `InterpExprs` itself. We define
them as follows:

```dafny
lemma InductExprs_Nil(st: S)
  ensures !Pes_Fail(st, []) ==> Pes_Succ(st, [], st, NilVS)

lemma InductExprs_Cons(st: S, e: Expr, es: seq<Expr>)
  ensures P_Fail(st, e) ==> Pes_Fail(st, [e] + es)
  ensures !P_Fail(st, e) ==> forall st1, v :: P_Succ(st, e, st1, v) && Pes_Fail(st1, es) ==> Pes_Fail(st, [e] + es)
  ensures forall st1, v, st2, vs :: P_Succ(st, e, st1, v) && Pes_Succ(st1, es, st2, vs) ==> Pes_Succ(st, [e] + es, st2, AppendValue(v, vs))
```

**Note**: We grouped several cases in `InductExprs_Cons` and used forall quantifiers. The reason
is that those proofs are rarely a problem: they are very similar to the `if then else`
case, in the sense that we often only need to have the induction hypotheses properly instantiated
in the context, and the context often remains small. We do however want to split cases and control
the context in cases like `Bind`, which often require a fair amount of work for
non-trivial proofs (e.g., when studying variable inlining).

### Updating the proofs

Interestingly, the proofs for `Pure`, and `EliminateMulZero` only require
introducing new definitions (for `Pes` for instance). They do not require actually
updating broken proofs. In addition, proving the `InductExprs_Cons` lemma for `VarUnchanged`
also requires writing an assertion to help the SMT solver.

The proof of correctness of `IsPure` that doesn't use the induction principle
(`PureNoInductionPrinciple`) is a bit more tedious, because it requires changing the `Seq`
case and introducing a proof about `InterpExprs`.

<a id="section-increments-varseq"></a>

### Declaring or updating several variables at once: `var x, y, w := 1, 2, 3;`

Now that we introduced a way of reasoning about sequences of expressions, we can update
`Bind` and `Assign` to allow updating/introducing several variables at once! We do the following
updates in the AST:

```dafny
Bind(bvar: string, bval: Expr, body: Expr)   -->   Bind(bvars: seq<string>, bvals: seq<Expr>, body: Expr)
Assign(avar: string, aval: Expr)             -->   Assign(avars: seq<string>, avals: seq<Expr>)
```

**Note:** In the [code development](induction-principle/AST.dfy), we actually rename `Expr` to `Expr_Raw` and define
`Expr` as a subset type of `Expr_Raw` to enforce the fact that in the `Assign` and `Bind`
cases, we have the same number of variables in the left-hand side as of expressions in
the righ-hand side.

Updating the interpreter and the induction principle is then
straightforward. Interestingly, the proofs using the induction principle (`VarUnchanged`,
`Pure` and `EliminateMulZero`) only require updates to the definitions declared (and not
defined) by the induction principle: none of the proofs break.

As expected, the `PureNoInductionPrinciple` proof requires the `Assign` and `Bind` cases
to be updated.

**Note:** If you look at the number of lines of code, you will notice that updating or
providing the definitions required by the induction principle forces us to modify more lines
of code that updating the proofs when not using the induction principle. The question then
is how straightforward it is to update or provide those definitions, compared to the cost
of updating broken proofs when we don't use the induction principle. So far, we experienced
more pain when updating the proofs. It is also worth mentioning the fact that, in the
Dafny-in-Dafny project, proving *any* theorem without the induction principle proved to
be a big hassle, while the introduction of the induction principle drastically diminished
the pain.

<a id="pair-of-state"></a>

## A different kind of proof: manipulating a pair of states

So far, we only studied proofs which require using one context. This changes if we add
closures. One way of adding support for closures is to introduce a `Value` datatype,
where closures are defined by the context they capture, a sequence of input variables,
and their body:

```dafny
datatype Value
| Integer(i: int)
| Closure(ctx: Context, vars: seq<string>, body: Expr)
```

The problem when verifying compiler transformations is that we can't use Dafny's native
equality anymore, because local rewritings might modify the body of closures and hence their
values: we can't reason with a *syntactic* equality. We thus need to introduce a *semantic*
equality over values. This semantic equality would state that two closures are equal if,
when called on equal inputs (in the sense of this semantic equality), they evaluate
to equal results (in the sense of this semantic equality, again), in the spirit of the
following predicate:

```dafny
predicate EqValue_Closure(cv: Closure, cv': Closure)
{
  && |cv.vars| == |cv'.vars|
  && forall inputs, inputs' |
       && |inputs| == |inputs'| == |cv.vars|
       && (forall i | 0 <= i < |inputs| :: EqValue(inputs[i], inputs'[i])) ::
       var ctx := InitializeClosureCtx(cv.vars, inputs);
       var ctx' := InitializeClosureCtx(cv'.vars, inputs');
       EqResult(InterpExpr(cv.body, ctx), InterpExpr(cv'.body, ctx'))
}
```

**Note:** This predicate is simplified for the purpose of illustration. For the "real"
predicate, see the full [Dafny-in-Dafny development](https://github.com/dafny-lang/compiler-bootstrap/blob/1493872f6a38f23ff83408333e25190d4829904c/src/Semantics/Equiv.dfy#L202).

We now need to reason modulo this semantic equality. For instance, when proving that
a transformation `TR` is sound, we often prove a lemma of the following form:

```dafny
forall ctx, ctx' | EqCtx(ctx, cxt') :: EqResult(InterpExpr(e, ctx), InterpExpr(TR(e), ctx'))
```

Because of this, we often need to manipulate pairs of contexts, but also pairs of values
and pairs of sequences of values. You can find a (toy) proof manipulating pairs of states
in the [`Equiv`](induction-principle/Equiv.dfy) module. Here is an excerpt of the interesting definitions, which shows how
to properly instantiate the induction principle to manipulate those pairs of
states/values:

```dafny
datatype MState = MState(ctx: Context, ctx': Context)
datatype MValue = MValue(v: int, v': int)
datatype MSeqValue = MSeqValue(vs: seq<int>, vs': seq<int>)

type S = MState
type V = MValue
type VS = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

ghost const Zero: V := MValue(0, 0)

ghost const NilVS: VS := MSeqValue([], [])

function VS_Last ...
{
  var v := vs.vs[|vs.vs| - 1];
  var v' := vs.vs'[|vs.vs| - 1];
  MValue(v, v')
}
```
