# Advanced Topics

## Type Inference

TO BE WRITTEN



## Well-founded Functions and Extreme Predicates
This section is a tutorial on well-founded functions and extreme predicates.
We place it here in preparation for Section [#sec-class-types]
where function and predicate definitions are described.

Recursive functions are a core part of computer science and mathematics.
Roughly speaking, when the definition of such a function spells out a
terminating computation from given arguments, we may refer to
it as a _well-founded function_.  For example, the common factorial and
Fibonacci functions are well-founded functions.

There are also other ways to define functions.  An important case
regards the definition of a boolean function as an extreme solution
(that is, a least or greatest solution) to some equation.  For
computer scientists with interests in logic or programming languages,
these _extreme predicates_ are important because they describe the
judgments that can be justified by a given set of inference rules
(see, e.g., [@CamilleriMelham:InductiveRelations;
@Winskel:FormalSemantics;
  @LeroyGrall:CoinductiveBigStep; @Pierce:SoftwareFoundations;
  @NipkowKlein:ConcreteSemantics]).

To benefit from machine-assisted reasoning, it is necessary not just
to understand extreme predicates but also to have techniques for
proving theorems about them.  A foundation for this reasoning was
developed by Paulin-Mohring [@PaulinMohring:InductiveCoq] and is the
basis of the constructive logic supported by Coq [@Coq:book] as well
as other proof assistants [@BoveDybjerNorell:BriefAgda;
@SwamyEtAl:Fstar2011].  Essentially, the idea is to represent the
knowledge that an extreme predicate holds by the proof term by which
this knowledge was derived.  For a predicate defined as the least
solution, such proof terms are values of an inductive datatype (that
is, finite proof trees), and for the greatest solution, a coinductive
datatype (that is, possibly infinite proof trees).  This means that
one can use induction and coinduction when reasoning about these proof
trees.  Therefore, these extreme predicates are known as,
respectively, _inductive predicates_ and _coinductive predicates_ (or,
_co-predicates_ for short).  Support for extreme predicates is also
available in the proof assistants Isabelle [@Paulson:CADE1994] and HOL
[@Harrison:InductiveDefs].

Dafny supports both well-founded functions and extreme predicates.
This section is a tutorial that describes the difference in general
terms, and then describes novel syntactic support in Dafny for
defining and proving lemmas with extreme predicates.  Although Dafny's
verifier has at its core a first-order SMT solver, Dafny's logical
encoding makes it possible to reason about fixpoints in an automated
way.

The encoding for coinductive predicates in Dafny was described previously
[@LeinoMoskal:Coinduction] and is here described in Section
[#sec-co-inductive-datatypes].

### Function Definitions

To define a function $f \colon X \to Y$ in terms of itself, one can
write an equation like
~ Equation {#eq-general}
<p style="text-align: center;">
$$f = \mathcal{F}(f)$$  
</p>
~

where $\mathcal{F}$ is a non-recursive function of type
$(X \to Y) \to X \to Y$.  
Because it takes a function as an argument,
$\mathcal{F}$
is referred to as a _functor_ (or _functional_, but not to be
confused by the category-theory notion of a functor).
Throughout, I will assume that 
$\mathcal{F}(f)$
by itself is well defined,
for example that it does not divide by zero.  I will also assume that 
$f$
occurs
only in fully applied calls in 
$\mathcal{F}(f)$;
 eta expansion can be applied to
ensure this.  If 
$f$
is a `boolean` function, that is, if 
$Y$
is
the type of booleans, then I call 
$f$
a _predicate_.

For example, the common Fibonacci function over the
natural numbers can be defined by the equation
<p style="text-align: center;">
$$
\mathit{fib} = \lambda n \bullet\: \mathbf{if}\:n < 2 \:\mathbf{then}\: n \:\mathbf{else}\: \mathit{fib}(n-2) + \mathit{fib}(n-1)
$$
</p>

With the understanding that the argument $n$ is universally
quantified, we can write this equation equivalently as

~ Equation {#eq-fib}
<p style="text-align: center;">
$$
\mathit{fib}(n) = \mathbf{if}\:n < 2\:\mathbf{then}\:n\:\mathbf{else}\:\mathit{fib}(n-2)%2B\mathit{fib}(n-1)
$$
</p>
~


The fact that the function being defined occurs on both sides of the equation
causes concern that we might not be defining the function properly, leading to a
logical inconsistency.  In general, there
could be many solutions to an equation like [#eq-general] or there could be none.
Let's consider two ways to make sure we're defining the function uniquely.

TO BE WRITTEN - two-state functions and predicates

TO BE WRITTEN - functions with named results

TO BE WRITTEN - various kinds of arrow types: ~> -> -->

#### Well-founded Functions

A standard way to ensure that equation [#eq-general] has a unique solution in $f$ is
to make sure the recursion is well-founded, which roughly means that the
recursion terminates.  This is done by introducing any well-founded
relation $\ll$ on the domain of $f$ and making sure that the argument to each recursive
call goes down in this ordering.  More precisely, if we formulate [#eq-general] as
<p style="text-align: center;">
$$
f(x) = \mathcal{F}{'}(f)
$$
</p>

then we want to check $E \ll x$ for each call $f(E)$ in $f(x) = \mathcal{F}'(f)$.
When a function
definition satisfies  this _decrement condition_, then the function is said to be
_well-founded_.

For example, to check the decrement condition for $\mathit{fib}$
in [#eq-fib], we can pick $\ll$
to be the arithmetic less-than relation on natural numbers and check the
following, for any $n$:
<p style="text-align: center;"> $$ 2 \leq n \;\Longrightarrow\; n-2 \ll n \;\wedge\; n-1 \ll n $$
</p>

Note that we are entitled to use the antecedent 
$2 \leq n$ because that is the
condition under which the else branch in [#eq-fib] is evaluated.

A well-founded function is often thought of as "terminating" in the sense
that the recursive _depth_ in evaluating $f$
on any given argument is finite.  That is, there are no infinite descending chains
of recursive calls.  However, the evaluation of $f$ on a given argument
may fail to terminate, because its _width_ may be infinite.  For example, let $P$
be some predicate defined on the ordinals and let $\mathit{P}_\downarrow$ be a predicate on the
ordinals defined by the following equation:

<p style="text-align: center;">
$$
\mathit{P}\_\downarrow = P(o) \;\wedge\; \forall p \bullet\; p \ll o \;\Longrightarrow\; \mathit{P}\_\downarrow(p) 
$$
</p>


With $\ll$ as the usual ordering on ordinals, this equation satisfies the decrement
condition, but evaluating $\mathit{P}\_\downarrow(\omega)$ would require evaluating
$\mathit{P}\_\downarrow(n)$ for every natural number $n$.  However, what we are concerned
about here is to avoid mathematical inconsistencies, and that is
indeed a consequence of the decrement condition.

#### Example with Well-founded Functions {#sec-fib-example}

So that we can later see how inductive proofs are done in Dafny, let's prove that
for any $n$, $\mathit{fib}(n)$ is even iff $n$ is a multiple of $3$.
We split our task into
two cases.  If $n < 2$, then the property follows directly from the definition
of $\mathit{fib}$.  Otherwise, note that exactly one of the three numbers $n-2$, $n-1$, and $n$
is a multiple of 3.  If $n$ is the multiple of 3, then by invoking the
induction hypothesis on $n-2$
and $n-1$, we obtain that $\mathit{fib}(n-2) + \mathit{fib}(n-1)$ is the sum of two odd numbers,
which is even.  If $n-2$ or $n-1$ is a multiple of 3, then by invoking the induction
hypothesis on $n-2$ and $n-1$, we obtain that $\mathit{fib}(n-2) + \mathit{fib}(n-1)$ is the sum of an
even number and an odd number, which is odd.  In this proof, we invoked the induction
hypothesis on $n-2$ and on $n-1$.  This is allowed, because both are smaller than
$n$, and hence the invocations go down in the well-founded ordering on natural numbers.

#### Extreme Solutions

We don't need to exclude the possibility of equation [#eq-general] having multiple
solutions---instead, we can just be clear about which one of them we want.
Let's explore this, after a smidgen of lattice theory.

For any complete lattice $(Y,\leq)$ and any set $X$, we can by _pointwise extension_ define
a complete lattice $(X \to Y, \dot{\Rightarrow})$, where for any $f,g \colon X \to Y$,


Equation
<p style="text-align: center;">
$$
f \dot{\Rightarrow} q  \;\;\equiv\;\; \forall x \bullet\; f(x) \leq g(x)
$$
</p>



In particular, if $Y$ is the set of booleans ordered by implication (`false` $\leq$ `true`),
then the set of predicates over any domain $X$ forms a complete lattice.
Tarski's Theorem [@Tarski:theorem] tells us that any monotonic function over a
complete lattice has a least and a greatest fixpoint.  In particular, this means that
$\mathcal{F}$ has a least fixpoint and a greatest fixpoint, provided $\mathcal{F}$ is monotonic.

Speaking about the _set of solutions_ in $f$ to [#eq-general] is the same as speaking
about the _set of fixpoints_ of functor $\mathcal{F}$.  In particular, the least and greatest
solutions to [#eq-general] are the same as the least and greatest fixpoints of $\mathcal{F}$.
In casual speak, it happens that we say "fixpoint of [#eq-general]", or more
grotesquely, "fixpoint of $f$" when we really mean "fixpoint of $\mathcal{F}$".

In conclusion of our little excursion into lattice theory, we have that, under the
proviso of $\mathcal{F}$ being monotonic, the set of solutions in $f$ to [#eq-general] is nonempty,
and among these solutions, there is in the $\dot{\Rightarrow}$ ordering a least solution (that is,
a function that returns `false` more often than any other) and a greatest solution (that
is, a function that returns `true` more often than any other).

When discussing extreme solutions, I will now restrict my attention to boolean functions
(that is, with $Y$ being the type of booleans).  Functor $\mathcal{F}$ is monotonic
if the calls to $f$ in $\mathcal{F}'(f)$ are in _positive positions_ (that is, under an even number
of negations).  Indeed, from now on, I will restrict my attention to such monotonic
functors $\mathcal{F}$.

Let me introduce a running example.  Consider the following equation,
where $x$ ranges over the integers:

~ Equation {#eq-EvenNat}
<p style="text-align: center;">
$$
g(x) = (x = 0 \:\vee\: g(x-2)) 
$$
</p>
~

This equation has four solutions in $g$.  With $w$ ranging over the integers, they are:


Equation
<p style="text-align: center;">
$$
 \begin{array}{r@{}l}
  g(x) \;\;\equiv\;\;{}&  x \in \{w \;|\; 0 \leq w \;\wedge\; w\textrm{ even}\} \\
  g(x) \;\;\equiv\;\;{}&  x \in \{w \;|\; w\textrm{ even}\} \\
  g(x) \;\;\equiv\;\;{}&  x \in \{w \;|\; (0 \leq w \;\wedge\; w\textrm{ even}) \:\vee\: w\textrm{ odd}\} \\
  g(x) \;\;\equiv\;\;{}&  x \in \{w \;|\; \mathit{true}\}
  \end{array} 
$$
</p>


The first of these is the least solution and the last is the greatest solution.

In the literature, the definition of an extreme predicate is often given as a set of
_inference rules_.  To designate the least solution, a single line separating the
antecedent (on top) from conclusion (on bottom) is used:

Equation {#g-ind-rule}
  $\frac{}{g(0)} \qquad\qquad \frac{g(x-2)}{g(x)}$

Through repeated applications of such rules, one can show that the predicate holds for
a particular value.  For example, the _derivation_, or _proof tree_,
to the left in Figure [#fig-proof-trees] shows that $g(6)$ holds.
(In this simple example, the derivation is a rather degenerate proof "tree".)
The use of these inference rules gives rise to a least solution, because proof trees are
accepted only if they are _finite_.

When inference rules are to designate the greatest solution, a thick
line is used:

~ Equation {#g-coind-rule}
    $\genfrac{}{}{1.2pt}0{}{g(0)}
  \qquad\qquad
    \genfrac{}{}{1.2pt}0{g(x-2)}{g(x)}$

In this case, proof trees are allowed to be infinite. 
For example, the left-hand example below shows a finite proof tree that uses the rules of [#g-ind-rule] to establish $g(6)$.  On the right is a partial depiction of an infinite proof tree that uses the rules of [#g-coind-rule] to establish $g(1)$.

<p style="text-align: center;">
$$\dfrac{
  \dfrac{
    \dfrac{
      \dfrac{}{g(0)}
      }{g(2)}
    }{g(4)}
  }{g(6)}
\qquad\qquad
\genfrac{}{}{1.2pt}0{
  \genfrac{}{}{1.2pt}0{
    \genfrac{}{}{1.2pt}0{
      \genfrac{}{}{1.2pt}0{
          {} {\vdots }
        }{g(-5)}
      }{g(-3)}
    }{g(-1)}
  }{g(1)}$$
</p>


Note that derivations may not be unique.  For example, in the case of the greatest
solution for $g$, there are two proof trees that establish $g(0)$:  one is the finite
proof tree that uses the left-hand rule of [#g-coind-rule] once, the other is the infinite
proof tree that keeps on using the right-hand rule of [#g-coind-rule].

### Working with Extreme Predicates

In general, one cannot evaluate whether or not an extreme predicate holds for some
input, because doing so may take an infinite number of steps.  For example, following
the recursive calls in the definition [#eq-EvenNat] to try to evaluate $g(7)$ would never
terminate.  However, there are useful ways to establish that an extreme predicate holds
and there are ways to make use of one once it has been established.

For any $\mathcal{F}$ as in [#eq-general], I define two infinite series of well-founded
functions, ${ {}^{\flat}\!f}_k$ and ${ {}^{\sharp}\!f}_k$
where $k$ ranges over the natural numbers:

~ Equation {#eq-least-approx}
<p style="text-align: center;">$$
   { {}^{\flat}\!f}_k(x) = \left\{
    \begin{array}{ll}
      \mathit{false}         & \textrm{if } k = 0 \\
      \mathcal{F}({ {}^{\flat}\!f}_{k-1})(x) & \textrm{if } k > 0 
    \end{array}
     \right\} $$.</p>
~
~ Equation {#eq-greatest-approx}
<p style="text-align: center;">$$
   { {}^{\sharp}\!f}_k(x) = \left\{
    \begin{array}{ll}
      \mathit{true}          & \textrm{if } k = 0 \\
      \mathcal{F}({ {}^{\sharp}\!f}_{k-1})(x) & \textrm{if } k > 0 
    \end{array}
    \right\} $$.</p>
~

These functions are called the _iterates_ of $f$, and I will also refer to them
as the _prefix predicates_ of $f$ (or the _prefix predicate_ of $f$, if we think
of $k$ as being a parameter).
Alternatively, we can define ${ {}^{\flat}\!f}_k$ and ${ {}^{\sharp}\!f}_k$ without mentioning $x$:
Let $\bot$ denote the function that always returns `false`, let $\top$
denote the function that always returns `true`, and let a superscript on $\mathcal{F}$ denote
exponentiation (for example, $\mathcal{F}^0(f) = f$ and $\mathcal{F}^2(f) = \mathcal{F}(\mathcal{F}(f))$).
Then, [#eq-least-approx] and [#eq-greatest-approx] can be stated equivalently as
${ {}^{\flat}\!f}_k = \mathcal{F}^k(\bot)$ and ${ {}^{\sharp}\!f}_k = \mathcal{F}^k(\top)$.

For any solution $f$ to equation [#eq-general], we have, for any $k$ and $\ell$
such that $k \leq \ell$:


Equation {#eq-prefix-postfix}
<p style="text-align: center;">$$
 { {}^{\flat}\!f}_k    \quad\;\dot{\Rightarrow}\;\quad { {}^{\flat}\!f}_\ell \quad\;\dot{\Rightarrow}\;\quad f      \quad\;\dot{\Rightarrow}\;\quad { {}^{\sharp}\!f}_\ell \quad\;\dot{\Rightarrow}\;\quad { {}^{\sharp}\!f}_k $$</p>

In other words, every ${ {}^{\flat}\!f}_k$ is a _pre-fixpoint_ of $f$ and every ${ {}^{\sharp}\!f}_k$ is a _post-fixpoint_
of $f$.  Next, I define two functions, $f^{\downarrow}$ and $f^{\uparrow}$, in
terms of the prefix predicates:


Equation {#eq-least-is-exists}
<p style="text-align: center;">$$
 f^{\downarrow}(x) \;=\;  \exists k \bullet\; { {}^{\flat}\!f}_k(x) $$</p>
Equation {#eq-greatest-is-forall}
<p style="text-align: center;">$$
  f^{\uparrow}(x) \;=\;  \forall k \bullet\; { {}^{\sharp}\!f}_k(x) $$</p>


By [#eq-prefix-postfix], we also have that $f^{\downarrow}$ is a pre-fixpoint of $\mathcal{F}$ and $f^{\uparrow}$
is a post-fixpoint of $\mathcal{F}$.  The marvelous thing is that, if $\mathcal{F}$ is _continuous_, then
$f^{\downarrow}$ and $f^{\uparrow}$ are the least and greatest fixpoints of $\mathcal{F}$.
These equations let us do proofs by induction when dealing with extreme predicates.
I will explain in Section [#sec-friendliness] how to check for continuity.

Let's consider two examples, both involving function $g$ in
[#eq-EvenNat].  As it turns out, $g$'s defining functor is continuous,
and therefore I will write $g^{\downarrow}$ and $g^{\uparrow}$ to denote the
least and greatest solutions for $g$ in [#eq-EvenNat].

#### Example with Least Solution {#sec-example-least-solution}

The main technique for establishing that $g^{\downarrow}(x)$ holds for some
$x$, that is, proving something of the form $Q \;\Longrightarrow\; g^{\downarrow}(x)$, is to
construct a proof tree like the one for $g(6)$ in Figure
[#fig-proof-trees].  For a proof in this direction, since we're just
applying the defining equation, the fact that
we're using a least solution for $g$ never plays a role (as long as we
limit ourselves to finite derivations).

The technique for going in the other direction, proving something _from_ an established
$g^{\downarrow}$ property, that is, showing something of the form $g^{\downarrow}(x) \;\Longrightarrow\; R$, typically
uses induction on the structure of the proof tree.  When the antecedent of our proof
obligation includes a predicate term $g^{\downarrow}(x)$, it is sound to
imagine that we have been given a proof tree for $g^{\downarrow}(x)$.  Such a proof tree
would be a data structure---to be more precise, a term in an
_inductive datatype_.
For this reason, least solutions like $g^{\downarrow}$ have been given the
name _inductive predicate_.

Let's prove $g^{\downarrow}(x) \;\Longrightarrow\; 0 \leq x \;\wedge\; x \textrm{ even}$.
We split our task into two cases, corresponding to which of the two
proof rules in [#g-ind-rule] was the
last one applied to establish $g^{\downarrow}(x)$.  If it was the left-hand rule, then $x=0$,
which makes it easy to establish the conclusion of our proof goal.  If it was the
right-hand rule, then we unfold the proof tree one level and obtain $g^{\downarrow}(x-2)$.
Since the proof tree for $g^{\downarrow}(x-2)$ is smaller than where we started, we invoke
the _induction hypothesis_ and obtain $0 \leq (x-2) \;\wedge\; (x-2) \textrm{ even}$, from which
it is easy to establish the conclusion of our proof goal.

Here's how we do the proof formally using [#eq-least-is-exists].  We massage the
general form of our proof goal:

|   | $f^{\uparrow}(x) \;\Longrightarrow\; R$                                                    |
| = | &nbsp;&nbsp;&nbsp;&nbsp; { [#eq-least-is-exists] }                        |
|   | $(\\exists k \bullet\; { {}^{\flat}\!f}_k(x)) \;\Longrightarrow\; R$                              |
| = | &nbsp;&nbsp;&nbsp;&nbsp; { distribute $\;\Longrightarrow\;$ over $\exists$ to the left } |
|   | $\forall k \bullet\; ({ {}^{\flat}\!f}_k(x) \;\Longrightarrow\; R)$                              |

The last line can be proved by induction over $k$.  So, in our case, we prove
${ {}^{\flat}\!g}\_k(x) \Longrightarrow 0 \leq x \wedge x \textrm{ even}$ for every $k$.
If $k = 0$, then ${ {}^{\flat}\!g}\_k(x)$ is `false`, so our goal holds trivially.
If $k > 0$, then ${ {}^{\flat}\!g}\_k(x) = (x = 0 \:\vee\: { {}^{\flat}\!g}\_{k-1}(x-2))$.  Our goal holds easily
for the first disjunct ($x=0$).  For the other disjunct,
we apply the induction hypothesis (on the smaller $k-1$ and with $x-2$) and
obtain $0 \leq (x-2)\;\wedge\; (x-2) \textrm{ even}$, from which our proof goal
follows.

#### Example with Greatest Solution {#sec-example-greatest-solution}

We can think of a given predicate $g^{\uparrow}(x)$ as being represented
by a proof tree---in this case a term in a _coinductive datatype_,
since the proof may be infinite.
For this reason, greatest solutions like $g^{\uparrow}$ have
been given the name _coinductive predicate_, or _co-predicate_ for short.
The main technique for proving something from a given proof tree, that
is, to prove something of the form $g^{\uparrow}(x) \;\Longrightarrow\; R$, is to
destruct the proof.  Since this is just unfolding the defining
equation, the fact that we're using a greatest solution for $g$ never
plays a role (as long as we limit ourselves to a finite number of
unfoldings).

To go in the other direction, to establish a predicate defined as a greatest solution,
like $Q \;\Longrightarrow\; g^{\uparrow}(x)$, we may need an infinite number of steps.  For this purpose,
we can use induction's dual, _coinduction_.  Were it not for one little detail, coinduction
is as simple as continuations in programming: the next part of the proof obligation
is delegated to the _coinduction hypothesis_.  The little detail is making sure that
it is the "next" part we're passing on for the continuation, not the same part.  This
detail is called _productivity_ and corresponds to the requirement in
induction of making sure we're going down a well-founded relation when
applying the induction hypothesis.  There are
many sources with more information, see for example the classic account by
Jacobs and Rutten [@JacobsRutten:IntroductionCoalgebra]
or a new attempt by Kozen and Silva
that aims to emphasize the simplicity, not the mystery, of
coinduction [@KozenSilva:Coinduction].

Let's prove $\mathit{true} \;\Longrightarrow\; g^{\uparrow}(x)$.  The intuitive coinductive proof goes like this:
According to the right-hand rule of [#g-coind-rule], $g^{\uparrow}(x)$ follows if we
establish $g^{\uparrow}(x-2)$, and that's easy to do by invoking the coinduction hypothesis.
The "little detail", productivity, is satisfied in this proof because we applied
a rule in [#g-coind-rule] before invoking the coinduction hypothesis.

For anyone who may have felt that the intuitive proof felt too easy, here is a formal
proof using [#eq-greatest-is-forall], which relies only on induction.  We massage the
general form of our proof goal:

<!--
|~~~|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|
|   | $Q \;\Longrightarrow\; f^{\uparrow}(x)$                                                      |
| = | &nbsp;&nbsp;&nbsp;&nbsp;  { [#eq-greatest-is-forall] }                      |
|   | $Q \;\Longrightarrow\; \forall k \bullet\; { {}^{\sharp}\!f}_k(x)$                                  |
| = | &nbsp;&nbsp;&nbsp;&nbsp;  { distribute $\;\Longrightarrow\;$ over $\forall$ to the right } |
|   | $\forall k \bullet\; Q \;\Longrightarrow\; { {}^{\sharp}\!f}_k(x)$                                  |
-->

The last line can be proved by induction over $k$.  So, in our case, we prove
<!--
$\mathit{true} \;\Longrightarrow\; { {}^{\sharp}\!g}_k(x)$ for every $k$.
If $k=0$, then ${ {}^{\sharp}\!g}_k(x)$ is $\mathit{true}$, so our goal holds trivially.
If $k > 0$, then ${ {}^{\sharp}\!g}_k(x) = (x = 0 \:\vee\: { {}^{\sharp}\!g}_{k-1}(x-2))$.  We establish the second
disjunct by applying the induction hypothesis (on the smaller $k-1$ and with $x-2$).
-->

### Other Techniques

Although in this paper I consider only well-founded functions and extreme
predicates, it is worth mentioning that there are additional ways of making sure that
the set of solutions to [#eq-general] is nonempty.  For example, if all calls to $f$ in
$\mathcal{F}'(f)$ are _tail-recursive calls_, then (under the assumption that $Y$ is nonempty) the set of
solutions is nonempty.  To see this, consider an attempted evaluation of $f(x)$ that fails
to determine a definite result value because of an infinite chain of calls that applies $f$
to each value of some subset $X'$ of $X$.  Then, apparently, the value of $f$ for any one
of the values in $X'$ is not determined by the equation, but picking any particular result
values for these makes for a consistent definition.
This was pointed out by Manolios and Moore [@ManoliosMoore:PartialFunctions].
Functions can be underspecified in this way in the proof assistants ACL2 [@ACL2:book]
and HOL [@Krauss:PhD].

## Functions in Dafny

In this section, I explain with examples the support in
Dafny[^fn-on-da-web] for well-founded functions, extreme predicates,
and proofs regarding these.

[^fn-on-da-web]: Dafny is open source at [dafny.codeplex.com](http://dafny.codeplex.com) and can also be used online at [rise4fun.com/dafny](http://rise4fun.com/dafny).

### Well-founded Functions in Dafny

Declarations of well-founded functions are unsurprising.  For example, the Fibonacci
function is declared as follows:

```dafny
function fib(n: nat): nat
{
  if n < 2 then n else fib(n-2) + fib(n-1)
}
```

Dafny verifies that the body (given as an expression in curly braces) is well defined.
This includes decrement checks for recursive (and mutually recursive) calls.  Dafny
predefines a well-founded relation on each type and extends it to lexicographic tuples
of any (fixed) length.  For example, the well-founded relation $x \ll y$ for integers
is $x < y \;\wedge\; 0 \leq y$, the one for reals is $x \leq y - 1.0 \;\wedge\; 0.0 \leq y$
(this is the same ordering as for integers, if you read the integer
relation as $x \leq y - 1 \;\wedge\; 0 \leq y$), the one for inductive
datatypes is structural inclusion,
and the one for coinductive datatypes is `false`.

Using a `decreases` clause, the programmer can specify the term in this predefined
order.  When a function definition omits a `decreases` clause, Dafny makes a simple
guess.  This guess (which can be inspected by hovering over the function name in the
Dafny IDE) is very often correct, so users are rarely bothered to provide explicit
`decreases` clauses.

If a function returns `bool`, one can drop the result type `: bool` and change the
keyword `function` to `predicate`.

### Proofs in Dafny

Dafny has `lemma` declarations.  These are really just special cases of methods:
they can have pre- and postcondition specifications and their body is a code block.
Here is the lemma we stated and proved in Section [#sec-fib-example]:

```dafny
lemma FibProperty(n: nat)
  ensures fib(n) % 2 == 0 <==> n % 3 == 0
{
  if n < 2 {
  } else {
    FibProperty(n-2); FibProperty(n-1);
  }
}
```

The postcondition of this lemma (keyword `ensures`) gives the proof
goal.  As in any program-correctness logic (e.g.,
[@Hoare:AxiomaticBasis]), the postcondition must
be established on every control path through the lemma's body.  For
`FibProperty`, I give the proof by
an `if` statement, hence introducing a case split.  The then branch is empty, because
Dafny can prove the postcondition automatically in this case.  The else branch
performs two recursive calls to the lemma.  These are the invocations of the induction
hypothesis and they follow the usual program-correctness rules,
namely: the precondition must hold at the call site, the call must terminate, and then
the caller gets to assume the postcondition upon return.  The "proof glue" needed
to complete the proof is done automatically by Dafny.

Dafny features an aggregate statement using which it is possible to make (possibly
infinitely) many calls at once.  For example, the induction hypothesis can be called
at once on all values `n'` smaller than `n`:

```dafny
forall n' | 0 <= n' < n {
  FibProperty(n');
}
```

For our purposes, this corresponds to _strong induction_.  More
generally, the `forall` statement has the form

```dafny
forall k | P(k)
  ensures Q(k)
{ Statements; }
```

Logically, this statement corresponds to _universal introduction_: the body proves that
`Q(k)` holds for an arbitrary `k` such that `P(k)`, and the conclusion of the `forall` statement
is then $\forall k \bullet\; P(k) \;\Longrightarrow\; Q(k)$.  When the body of the `forall` statement is
a single call (or `calc` statement), the `ensures` clause is inferred and can be omitted,
like in our `FibProperty` example.

Lemma `FibProperty` is simple enough that its whole body can be replaced by the one
`forall` statement above.  In fact, Dafny goes one step further: it automatically
inserts such a `forall` statement at the beginning of every lemma [@Leino:induction].
Thus, `FibProperty` can be declared and proved simply by:

```dafny
lemma FibProperty(n: nat)
  ensures fib(n) % 2 == 0 <==> n % 3 == 0
{ }
```

Going in the other direction from universal introduction is existential elimination,
also known as Skolemization.  Dafny has a statement for this, too:
for any variable `x` and boolean expression `Q`, the
_assign such that_ statement `x :| Q;` says to assign to `x` a value such that `Q`
will hold.  A proof obligation when using this statement is to show that there
exists an `x` such that `Q` holds.  For example, if the fact
$\\exists k \bullet\; 100 \leq \mathit{fib}(k) < 200$ is known, then the statement
`k :| 100 <= fib(k) < 200;` will assign to `k` some value (chosen arbitrarily)
for which `fib(k)` falls in the given range.

### Extreme Predicates in Dafny {#sec-friendliness}

In this previous subsection, I explained that a `predicate` declaration introduces a
well-founded predicate.  The declarations for introducing extreme predicates are
`inductive predicate` and `copredicate`.  Here is the definition of the least and
greatest solutions of $g$ from above, let's call them `g` and `G`:

```dafny
inductive predicate g(x: int) { x == 0 || g(x-2) }
copredicate G(x: int) { x == 0 || G(x-2) }
```

When Dafny receives either of these definitions, it automatically declares the corresponding
prefix predicates.  Instead of the names ${ {}^{\flat}\!g}_k$ and ${ {}^{\sharp}\!g}_k$ that I used above, Dafny
names the prefix predicates `g#[k]` and `G#[k]`, respectively, that is, the name of
the extreme predicate appended with `#`, and the subscript is given as an argument in
square brackets.  The definition of the prefix predicate derives from the body of
the extreme predicate and follows the form in [#eq-least-approx] and [#eq-greatest-approx].
Using a faux-syntax for illustrative purposes, here are the prefix
predicates that Dafny defines automatically from the extreme
predicates `g` and `G`:

```dafny
predicate g#[_k: nat](x: int) { _k != 0 && (x == 0 || g#[_k-1](x-2)) }
predicate G#[_k: nat](x: int) { _k != 0 ==> (x == 0 || G#[_k-1](x-2)) }
```

The Dafny verifier is aware of the connection between extreme predicates and their
prefix predicates, [#eq-least-is-exists] and [#eq-greatest-is-forall].

Remember that to be well defined, the defining functor of an extreme predicate
must be monotonic, and for [#eq-least-is-exists] and [#eq-greatest-is-forall] to hold,
the functor must be continuous.  Dafny enforces the former of these by checking that
recursive calls of extreme predicates are in positive positions.  The continuity
requirement comes down to checking that they are also in _continuous positions_:
that recursive calls to inductive predicates are
not inside unbounded universal quantifiers and that recursive calls to co-predicates
are not inside unbounded existential quantifiers [@Milner:CCS; @LeinoMoskal:Coinduction].

### Proofs about Extreme Predicates

From what I have presented so far, we can do the formal proofs from Sections
[#sec-example-least-solution] and [#sec-example-greatest-solution].  Here is the
former:

```dafny
lemma EvenNat(x: int)
  requires g(x)
  ensures 0 <= x && x % 2 == 0
{
  var k: nat :| g#[k](x);
  EvenNatAux(k, x);
}
lemma EvenNatAux(k: nat, x: int)
  requires g#[k](x)
  ensures 0 <= x && x % 2 == 0
{
  if x == 0 { } else { EvenNatAux(k-1, x-2); }
}
```

Lemma `EvenNat` states the property we wish to prove.  From its
precondition (keyword `requires`) and
[#eq-least-is-exists], we know there is some `k` that will make the condition in the
assign-such-that statement true.  Such a value is then assigned to `k` and passed to
the auxiliary lemma, which promises to establish the proof goal.  Given the condition
`g#[k](x)`, the definition of `g#` lets us conclude `k != 0` as well as the disjunction
`x == 0 || g#[k-1](x-2)`.  The then branch considers the case of the first disjunct,
from which the proof goal follows automatically.  The else branch can then assume
`g#[k-1](x-2)` and calls the induction hypothesis with those parameters.  The proof
glue that shows the proof goal for `x` to follow from the proof goal with `x-2` is
done automatically.

Because Dafny automatically inserts the statement

```dafny
forall k', x' | 0 <= k' < k && g#[k'](x') {
  EvenNatAux(k', x');
}
```

at the beginning of the body of `EvenNatAux`, the body can be left empty and Dafny
completes the proof automatically.

Here is the Dafny program that gives the proof from Section [#sec-example-greatest-solution]:

```dafny
lemma Always(x: int)
  ensures G(x)
{ forall k: nat { AlwaysAux(k, x); } }
lemma AlwaysAux(k: nat, x: int)
  ensures G#[k](x)
{ }
```

While each of these proofs involves only basic proof rules, the setup feels a bit clumsy,
even with the empty body of the auxiliary lemmas.  Moreover,
the proofs do not reflect the intuitive proofs I described in
Section [#sec-example-least-solution] and [#sec-example-greatest-solution].
These shortcoming are addressed in the next subsection.

### Nicer Proofs of Extreme Predicates

The proofs we just saw follow standard forms:
use Skolemization to convert the inductive predicate into a prefix predicate for some `k`
and then do the proof inductively over `k`; respectively,
by induction over `k`, prove the prefix predicate for every `k`, then use
universal introduction to convert to the coinductive predicate.
With the declarations `inductive lemma` and `colemma`, Dafny offers to
set up the proofs
in these standard forms.  What is gained is not just fewer characters in the program
text, but also a possible intuitive reading of the proofs.  (Okay, to be fair, the
reading is intuitive for simpler proofs; complicated proofs may or may not be intuitive.)

Somewhat analogous to the creation of prefix predicates from extreme predicates, Dafny
automatically creates a _prefix lemma_ `L#` from each "extreme lemma" `L`.  The pre-
and postconditions of a prefix lemma are copied from those of the extreme lemma,
except for the following replacements:
For an inductive lemma, Dafny looks in the precondition to find calls (in positive, continuous
positions) to inductive predicates `P(x)` and replaces these with `P#[_k](x)`.
For a
co-lemma, Dafny looks in the postcondition to find calls (in positive, continuous positions)
to co-predicates `P` (including equality among coinductive datatypes, which is a built-in
co-predicate) and replaces these with `P#[_k](x)`.
In each case, these predicates `P` are the lemma's _focal predicates_.

The body of the extreme lemma is moved to the prefix lemma, but with
replacing each recursive
call `L(x)` with `L#[_k-1](x)` and replacing each occurrence of a call
to a focal predicate
`P(x)` with `P#[_k-1](x)`.  The bodies of the extreme lemmas are then replaced as shown
in the previous subsection.  By construction, this new body correctly leads to the
extreme lemma's postcondition.

Let us see what effect these rewrites have on how one can write proofs.  Here are the proofs
of our running example:

```dafny
inductive lemma EvenNat(x: int)
  requires g(x)
  ensures 0 <= x && x % 2 == 0
{ if x == 0 { } else { EvenNat(x-2); } }
colemma Always(x: int)
  ensures G(x)
{ Always(x-2); }
```

Both of these proofs follow the intuitive proofs given in Sections
[#sec-example-least-solution] and [#sec-example-greatest-solution].  Note that in these
simple examples, the user is never bothered with either prefix predicates nor
prefix lemmas---the proofs just look like "what you'd expect".

Since Dafny automatically inserts calls to the induction hypothesis at the beginning of
each lemma, the bodies of the given extreme lemmas `EvenNat` and
`Always` can be empty and Dafny still completes the proofs.
Folks, it doesn't get any simpler than that!

## Variable Initialization and Definite Assignment

TO BE WRITTEN -- rules for default initialization; resulting rules for constructors; definite assignment rules

## Well-founded Orders {#sec-well-founded-orders}

TODO: Write this section

## Module Refinement {#sec-module-refinement}

TODO: Write this section.

