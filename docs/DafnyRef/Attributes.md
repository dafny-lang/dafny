# 22. Attributes
````grammar
Attribute = "{:" AttributeName [ Expressions ] "}"
````
Dafny allows many of its entities to be annotated with _Attributes_.
The grammar shows where the attribute annotations may appear.

Here is an example of an attribute from the Dafny test suite:

```dafny
{:MyAttribute "hello", "hi" + "there", 57}
```

In general an attribute may have any name the user chooses. It may be
followed by a comma-separated list of expressions. These expressions will
be resolved and type-checked in the context where the attribute appears.

In general, any Dafny entity may have a list of attributes.
Dafny does not check that the attributes listed for an entity
are appropriate for that entity (which means that misspellings may
go silently unnoticed).

## 22.1. Dafny Attributes
All entities that Dafny translates to Boogie have their attributes
passed on to Boogie except for the `{:axiom}` attribute (which
conflicts with Boogie usage) and the `{:trigger}` attribute which is
instead converted into a Boogie quantifier _trigger_. See Section 11 of
[@Leino:Boogie2-RefMan].

Dafny has special processing for some attributes. For some attributes, the
setting is only looked for on the entity with the attribute. For others, we start
at the entity and if the attribute is not there, look up in the hierarchy
(enclosing class and enclosing modules).
The attribute
declaration closest to the entity overrides those further away.

For attributes with a single boolean expression argument, the attribute
with no argument is interpreted as if it were true.

The attributes that are processed specially by Dafny are described in the
following sections.

### 22.1.1. assumption
This attribute can only be placed on a local ghost bool
variable of a method. Its declaration cannot have a rhs, but it is
allowed to participate as the lhs of exactly one assignment of the
form: `b := b && expr;`. Such a variable declaration translates in the
Boogie output to a declaration followed by an `assume b` command.
See [@LeinoWuestholz2015], Section 3, for example uses of the `{:assumption}`
attribute in Boogie.

### 22.1.2. autoReq boolExpr
For a function declaration, if this attribute is set true at the nearest
level, then its `requires` clause is strengthened sufficiently so that
it may call the functions that it calls.

For following example
```dafny
function f(x:int) : bool
  requires x > 3
{
  x > 7
}

// Should succeed thanks to auto_reqs
function {:autoReq} g(y:int, b:bool) : bool
{
  if b then f(y + 2) else f(2*y)
}
```
the `{:autoReq}` attribute causes Dafny to
deduce a `requires` clause for g as if it had been
declared
```dafny
function g(y:int, b:bool) : bool
  requires if b then y + 2 > 3 else 2 * y > 3
{
  if b then f(y + 2) else f(2*y)
}
```

### 22.1.3. autocontracts
Dynamic frames [@Kassios:FM2006;@SmansEtAl:VeriCool;@SmansEtAl:ImplicitDynamicFrames;
@LEINO:Dafny:DynamicFrames]
are frame expressions that can vary dynamically during
program execution. AutoContracts is an experimental feature that will
fill much of the dynamic-frames boilerplate into a class.

From the user's perspective, what needs to be done is simply:

* mark the class with {:autocontracts}
* declare a function (or predicate) called Valid()


AutoContracts will then:

*  Declare:
```dafny
   ghost var Repr: set<object>
```

* For function/predicate Valid(), insert:
```dafny
   reads this, Repr
```
* Into body of Valid(), insert (at the beginning of the body):
```dafny
   this in Repr && null !in Repr
```
* and also insert, for every array-valued field A declared in the class:
```dafny
   (A != null ==> A in Repr) &&
```
* and for every field F of a class type T where T has a field called Repr, also insert:
```dafny
   (F != null ==> F in Repr && F.Repr <= Repr && this !in Repr)
```
  Except, if A or F is declared with `{:autocontracts false}`, then the implication will not
be added.

* For every constructor, add:
```dafny
   modifies this
   ensures Valid() && fresh(Repr - {this})
```
* At the end of the body of the constructor, add:
```dafny
   Repr := {this};
   if (A != null) { Repr := Repr + {A}; }
   if (F != null) { Repr := Repr + {F} + F.Repr; }
```
* For every method, add:
```dafny
   requires Valid()
   modifies Repr
   ensures Valid() && fresh(Repr - old(Repr))
```
* At the end of the body of the method, add:
```dafny
   if (A != null) { Repr := Repr + {A}; }
   if (F != null) { Repr := Repr + {F} + F.Repr; }
```

### 22.1.4. axiom
The `{:axiom}` attribute may be placed on a function or method.
It means that the post-condition may be assumed to be true
without proof. In that case also the body of the function or
method may be omitted.

The `{:axiom}` attribute only prevents Dafny from verifying that the body matches the post-condition.
Dafny still verifies the well-formedness of pre-conditions, of post-conditions, and of the body if provided.
To prevent Dafny from running all these checks, one would use `{:verify false}`, which is not recommended.

### 22.1.5. compile
The `{:compile}` attribute takes a boolean argument. It may be applied to
any top-level declaration. If that argument is false, then that declaration
will not be compiled into .Net code.

### 22.1.6. decl
The `{:decl}` attribute may be placed on a method declaration. It
inhibits the error message that has would be given when the method has an
`ensures` clauses but no body. It has been used to declare Dafny interfaces
in the MSR IronClad and IronFleet projects. Instead the `extern` keyword
should be used (but that is soon to be replaced by the `{:extern}` attribute).

### 22.1.7. fuel
The fuel attributes is used to specify how much "fuel" a function should have,
i.e., how many times Z3 is permitted to unfold it's definition.  The
new {:fuel} annotation can be added to the function itself, it which
case it will apply to all uses of that function, or it can overridden
within the scope of a module, function, method, iterator, calc, forall,
while, assert, or assume.  The general format is:

```dafny
{:fuel functionName,lowFuel,highFuel}
```

When applied as an annotation to the function itself, omit
functionName.  If highFuel is omitted, it defaults to lowFuel + 1.

The default fuel setting for recursive functions is 1,2.  Setting the
fuel higher, say, to 3,4, will give more unfoldings, which may make
some proofs go through with less programmer assistance (e.g., with
fewer assert statements), but it may also increase verification time,
so use it with care.  Setting the fuel to 0,0 is similar to making the
definition opaque, except when used with all literal arguments.

### 22.1.8. heapQuantifier
The `{:heapQuantifier}` attribute may be used on a ``QuantifierExpression``.
When it appears in a quantifier expression, it is as if a new heap-valued
quantifier variable was added to the quantification. Consider this code
that is one of the invariants of a while loop.

```dafny
invariant forall u {:heapQuantifier} :: f(u) == u + r
```

The quantifier is translated into the following Boogie:

```
(forall q$heap#8: Heap, u#5: int ::
    {:heapQuantifier}
    $IsGoodHeap(q$heap#8) && ($Heap == q$heap#8 || $HeapSucc($Heap, q$heap#8))
       ==> $Unbox(Apply1(TInt, TInt, f#0, q$heap#8, $Box(u#5))): int == u#5 + r#0);
```

What this is saying is that the quantified expression, `f(u) == u + r`,
which may depend on the heap, is also valid for any good heap that is either the
same as the current heap, or that is derived from it by heap update operations.

### 22.1.9. imported
If a ``MethodDecl`` or ``FunctionDecl`` has an `{:imported}` attribute,
then it is allowed to have a empty body even though it has an **ensures**
clause. Ordinarily a body would be required in order to provide the
proof of the **ensures** clause (but the `(:axiom)` attribute also
provides this facility, so the need for `(:imported)` is not clear.)
A method or function declaration may be given the `(:imported)` attribute. This suppresses
the error message that would be given if a method or function with an `ensures` clause
does not have a body.

This seems to duplicate what `extern` and `{:decl}` do and would be a good candidate for
deprecation.

### 22.1.10. induction
The `{:induction}` attribute controls the application of
proof by induction to two contexts. Given a list of
variables on which induction might be applied, the
`{:induction}` attribute selects a sub-list of those
variables (in the same order) to which to apply induction.

Dafny issue [34](https://github.com/Microsoft/dafny/issues/34)
proposes to remove the restriction that the sub-list
be in the same order, and would apply induction in the
order given in the `{:induction}` attribute.

The two contexts are:

* A method, in which case the bound variables are all the
  in-parameters of the method.
* A quantifier expression, in which case the bound variables
  are the bound variables of the quantifier expression.

The form of the `{:induction}` attribute is one of the following:

* `{:induction}` -- apply induction to all bound variables
* `{:induction false}` -- suppress induction, that is, don't apply it to any bound variable
* `{:induction L}` where `L` is a list consisting entirely of bound variables
-- apply induction to the specified bound variables
* `{:induction X}` where `X` is anything else -- treat the same as
{:induction}, that is, apply induction to all bound variables. For this
usage conventionally `X` is `true`.

Here is an example of using it on a quantifier expression:
```dafny
lemma Fill_J(s: seq<int>)
  requires forall i :: 1 <= i < |s| ==> s[i-1] <= s[i]
  ensures forall i,j {:induction j} :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}
```

### 22.1.11. layerQuantifier
When Dafny is translating a quantified expression, if it has
a `{:layerQuantifier}` attribute an additional quantifier
variable is added to the quantifier bound variables.
This variable as the predefined _LayerType_.
A `{:layerQuantifier}` attribute may be placed on a quantifier expression.
Translation of Dafny into Boogie defines a _LayerType_ which has defined zero and
successor constructors.

The Dafny source has the comment that "if a function is recursive,
then make the reveal lemma quantifier a layerQuantifier."
And in that case it adds the attribute to the quantifier.

There is no explicit user of the `{:layerQuantifier}` attribute
in the Dafny tests. So I believe this attribute is only used
internally by Dafny and not externally.

TODO: Need more complete explanation of this attribute.
Dafny issue [35](https://github.com/Microsoft/dafny/issues/35) tracks
further effort for this attribute.

### 22.1.12. nativeType {#sec-nativetype}
The `{:nativeType}` attribute may only be used on a ``NewtypeDecl``
where the base type is an integral type. It can take one of the following
forms:

* `{:nativeType}` - With no parameters it has no effect and the ``NewtypeDecl``
have its default behavior which is to choose a native type that can hold any
value satisfying the constraints, if possible, otherwise BigInteger is used.
* `{:nativeType true}` - Also gives default ``NewtypeDecl`` behavior,
but gives an error if base type is not integral.
* `{:nativeType false}` - Inhibits using a native type. BigInteger is used
for integral types and BitRational for real types.
* `{:nativeType "typename"}` - This form has an native integral
type name as a string literal. Acceptable values are: "byte",
"sbyte", "ushort", "short", "uint", "int", "ulong" and "long".
An error is reported if the given datatype cannot hold all the
values that satisfy the constraint.


### 22.1.13. opaque {#sec-opaque}
Ordinarily the body of a function is transparent to its users but
sometimes it is useful to hide it. If a function `foo` or `bar` is given the
`{:opaque}` attribute, then Dafny hides the body of the function,
so that it can only be seen within its recursive clique (if any),
or if the programmer specifically asks to see it via the statement `reveal foo(), bar();`.

More information about the Boogie implementation of {:opaque} [here](https://github.com/dafny-lang/dafny/blob/master/docs/Compilation/Boogie.md).

<!--
Describe this where refinement is described, as appropriate.

-### 22.1.15. prependAssertToken
This is used internally in Dafny as part of module refinement.
It is an attribute on an assert statement.
The Dafny code has the following comment:

```dafny
// Clone the expression, but among the new assert's attributes, indicate
// that this assertion is supposed to be translated into a check.  That is,
// it is not allowed to be just assumed in the translation, despite the fact
// that the condition is inherited.
```

TODO: Decide if we want to describe this in more detail, or whether
the functionality is already adequately described where
refinement is described.
-->

### 22.1.14. tailrecursion
This attribute is used on method declarations. It has a boolean argument.

If specified with a false value, it means the user specifically
requested no tail recursion, so none is done.

If specified with a true value, or if no argument is specified,
then tail recursive optimization will be attempted subject to
the following conditions:

* It is an error if the method is a ghost method and tail
recursion was explicitly requested.
* Only direct recursion is supported, not mutually recursive methods.
* If `{:tailrecursion true}` was specified but the code does not allow it,
an error message is given.

### 22.1.15. timeLimitMultiplier
This attribute may be placed on a method or function declaration
and has an integer argument. If `{:timeLimitMultiplier X}` was
specified a `{:timelimit Y}` attributed is passed on to Boogie
where `Y` is `X` times either the default verification time limit
for a function or method, or times the value specified by the
Boogie `timelimit` command-line option.

### 22.1.16. trigger
Trigger attributes are used on quantifiers and comprehensions.
They are translated into Boogie triggers.

### 22.1.17. typeQuantifier
The `{:typeQuantifier}` attribute must be used on a quantifier if it
quantifies over types.


## 22.2. Boogie Attributes
Use the Boogie "/attrHelp" option to get the list of attributes
that Boogie recognizes and their meaning. Here is the output at
the time of this writing. Dafny passes attributes that have
been specified to Boogie.

```
Boogie: The following attributes are supported by this implementation.

  ---- On top-level declarations ---------------------------------------------

    {:ignore}
      Ignore the declaration (after checking for duplicate names).

    {:extern}
      If two top-level declarations introduce the same name (for example, two
      constants with the same name or two procedures with the same name), then
      Boogie usually produces an error message.  However, if at least one of
      the declarations is declared with :extern, one of the declarations is
      ignored.  If both declarations are :extern, Boogie arbitrarily chooses
      one of them to keep; otherwise, Boogie ignore the :extern declaration
      and keeps the other.

    {:checksum <string>}
      Attach a checksum to be used for verification result caching.

  ---- On implementations and procedures -------------------------------------

     {:inline N}
       Inline given procedure (can be also used on implementation).
       N should be a non-negative number and represents the inlining depth.
       With /inline:assume call is replaced with "assume false" once inlining depth is reached.
       With /inline:assert call is replaced with "assert false" once inlining depth is reached.
       With /inline:spec call is left as is once inlining depth is reached.
       With the above three options, methods with the attribute {:inline N} are not verified.
       With /inline:none the entire attribute is ignored.

     {:verify false}
       Skip verification of an implementation.

     {:vcs_max_cost N}
     {:vcs_max_splits N}
     {:vcs_max_keep_going_splits N}
       Per-implementation versions of
       /vcsMaxCost, /vcsMaxSplits and /vcsMaxKeepGoingSplits.

     {:selective_checking true}
       Turn all asserts into assumes except for the ones reachable from
       assumptions marked with the attribute {:start_checking_here}.
       Thus, "assume {:start_checking_here} something;" becomes an inverse
       of "assume false;": the first one disables all verification before
       it, and the second one disables all verification after.

     {:priority N}
       Assign a positive priority 'N' to an implementation to control the order
       in which implementations are verified (default: N = 1).

     {:id <string>}
       Assign a unique ID to an implementation to be used for verification
       result caching (default: "<impl. name>:0").

     {:timeLimit N}
       Set the time limit for a given implementation.

  ---- On functions ----------------------------------------------------------

     {:builtin "spec"}
     {:bvbuiltin "spec"}
       Rewrite the function to built-in prover function symbol 'fn'.

     {:inline}
     {:inline true}
       Expand function according to its definition before going to the prover.

     {:never_pattern true}
       Terms starting with this function symbol will never be
       automatically selected as patterns. It does not prevent them
       from being used inside the triggers, and does not affect explicit
       trigger annotations. Internally it works by adding {:nopats ...}
       annotations to quantifiers.

     {:identity}
     {:identity true}
       If the function has 1 argument and the use of it has type X->X for
       some X, then the abstract interpreter will treat the function as an
       identity function.  Note, the abstract interpreter trusts the
       attribute--it does not try to verify that the function really is an
       identity function.

  ---- On variables ----------------------------------------------------------

     {:existential true}
       Marks a global Boolean variable as existentially quantified. If
       used in combination with option /contractInfer Boogie will check
       whether there exists a Boolean assignment to the existentials
       that makes all verification conditions valid.  Without option
       /contractInfer the attribute is ignored.

  ---- On assert statements --------------------------------------------------

     {:subsumption n}
       Overrides the /subsumption command-line setting for this assertion.

     {:split_here}
       Verifies code leading to this point and code leading from this point
       to the next split_here as separate pieces.  May help with timeouts.
       May also occasionally double-report errors.

  ---- The end ---------------------------------------------------------------

```

However a scan of Boogie's sources shows it checks for the
following attributes.

* `{:$}`
* `{:$renamed$}`
* `{:InlineAssume}`
* `{:PossiblyUnreachable}`
* `{:__dominator_enabled}`
* `{:__enabled}`
* `{:a##post##}`
* `{:absdomain}`
* `{:ah}`
* `{:assumption}`
* `{:assumption_variable_initialization}`
* `{:atomic}`
* `{:aux}`
* `{:both}`
* `{:bvbuiltin}`
* `{:candidate}`
* `{:captureState}`
* `{:checksum}`
* `{:constructor}`
* `{:datatype}`
* `{:do_not_predicate}`
* `{:entrypoint}`
* `{:existential}`
* `{:exitAssert}`
* `{:expand}`
* `{:extern}`
* `{:hidden}`
* `{:ignore}`
* `{:inline}`
* `{:left}`
* `{:linear}`
* `{:linear_in}`
* `{:linear_out}`
* `{:msg}`
* `{:name}`
* `{:originated_from_invariant}`
* `{:partition}`
* `{:positive}`
* `{:post}`
* `{:pre}`
* `{:precondition_previous_snapshot}`
* `{:qid}`
* `{:right}`
* `{:selective_checking}`
* `{:si_fcall}`
* `{:si_unique_call}`
* `{:sourcefile}`
* `{:sourceline}`
* `{:split_here}`
* `{:stage_active}`
* `{:stage_complete}`
* `{:staged_houdini_tag}`
* `{:start_checking_here}`
* `{:subsumption}`
* `{:template}`
* `{:terminates}`
* `{:upper}`
* `{:verified_under}`
* `{:weight}`
* `{:yields}`


