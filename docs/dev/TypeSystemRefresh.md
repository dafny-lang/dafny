# Dafny type system refresh

## Overview

The "type system refresh" is a reimplementation of Dafny's name resolution, type inference, and type checking. In many ways, it just improves the organization of the implementation. This will allow Dafny's type system to continue to evolve. For example, it has already enabled the support of traits on datatypes, and it has been building with non-numeric newtypes in mind. Most of this document is concerned with the new implementation. But the new type system also makes some changes in the language that are not backward compatible. Those breaking changes are:

* An downcast from a trait to some type that implements the trait now requires an explicit cast (using `as`). Like the previous implicit cast, this explicit cast is checked statically.

    Other popular languages with static type checking also require such a cast. Note, subset types are unaffected by this change; for example, it is still possible to write an assignment from an `int` to a `nat` without an explicit cast.

* Equality-checking expressions (like `==`) no longer treat formal type parameters in a special way.

    Previously, Dafny allowed, for example, an `array<int>` and an `array<X>` to be compared, where `X` is a type parameter, on the grounds that `X` may be `int` and thus the two arrays could be equal. Since Dafny, now since many years, has an `as` operator, such a comparison can easily be expressed without a special case in the type system: `a == b as object`.

* The types of bound variables are inferred to be base types, not subset types. For example, bound variable `x` in `forall x :: P(x)` may be inferred to have type `int`, but never `nat`.

    This makes inference more predictable. It also removes the risk that, say, an intended quantifier `forall x: int :: P(x)` is instead inferred to be the logically weaker `forall x: nat :: P(x)`.

    (This design may soon change in one place, namely when a lambda expressions is known to be used in a limited number of places. This happens in array initializers and sequence comprehensions, where it would be friendly to try to infer the bound variable to be of type `nat` rather than `int`.)

The new type system also fixes a number of bugs in the previous type system. Among them are bugs having to do with cyclic dependencies among declarations, which the new type system is equipped to handle.

The rest of this document describes the implementation of the new type system.

## Pre-types and type adjustments

The earlier parts of the resolver are tricky, because of cyclic dependencies among the information that is to be computed. For example, to determine the type of an expression `o.f`, it is necessary to know what `f` is, which in turn requires knowing the type of `o`. As a concrete example, consider

``` dafny
class Cell {
  var data: bv32
  constructor (data: bv32) {
    this.data := data;
  }
}

method Tricky() {
  var c := null; // Cell?
  var s := 0; // bv32
  for i := 0 to 100 {
    if c == null {
      c := new Cell(s + 10);
    }
    s := s + c.data;
  }
}
```

For the expression `c.data` in the loop body, name resolution will determine that `c` is a local variable, then type inference will determine that the type of `c` is `Cell?`, then name resolution to look up `data` as a member in class `Cell`, and then type inference can determine the type of `c.data` to be `bv32`. (Type inference will then also determine that `s` has type `bv32`, and therefore that the literal `0` in the initial assignment to `s` also has type `bv32`.) So, name resolution and some part of type inference are mutually dependent.

Define _pre-type_ to be a type that is completed handled by the static type system, without the later help of the verifier. In other words, a pre-type is a type that does not involve subset types. It is the inference of pre-types that is mutually dependent on name resolution, because subset types do not introduce any type members (like the `.f` in the example above). This suggests separating name resolution and pre-type inference from the further inference of types with subset types. But there is also another reason for such a separation, namely that assignments in Dafny (like `x := E;`) obey standard subtyping rules for pre-types, whereas types with subset types do not. For example, the pre-type of `E` must be a subtype of the pre-type of `x`. The subset type `nat` is a subtype of the base type `int`, and the type system allow any combination of `x` and `E` being `int` or `nat`; in particular, it allows `E` to have type `int` and `x` to have type `nat`. By separating concerns regarding subset types from the initial inference where names are resolved, the tricky part of resolving names gets to use simpler type constraints.

After successfully completing pre-type inference, all names and operators have been resolved, and all expressions and variables have pre-types. Since subset types are the difference between pre-types and types, and since subset types are enforced by the verifier, one could imagine that type inference would be done. This is almost true, but not quite. For one, having only the pre-types means that the verifier has to work harder than necessary. For example, using the `Cell` class from above, consider the program

``` dafny
method Add(x: bv32, y: bv32) returns (r: bv32) {
  var c := new Cell(x);
  var d := new Cell(y);
  r := c.data + d.data;
}
```

The pre-types of `c` and `d` are `Cell?`. With just those types, the verifier would have to prove that `c` and `d` are non-null in the expressions `c.data` and `d.data`. However, if type inference could figure out that `c` and `d` have the non-null types `Cell` (recall, `Cell` in Dafny is a subset type with base type `Cell?`), then the verifier would not have anything to prove. There are also situations where the verifier would fail, because of lack of loop invariants. For example,

``` dafny
method Natural(m: nat, n: nat, s: seq<int>) returns (r: int) {
  var k := m;
  r := 0;
  for i := 0 to |s| {
    if k < |s| {
      r := r + s[k];
    }
    k := if k == m then n else m;
  }
}
```

The pre-type of `k` is `int`. With only that information about `k`, the operation `s[k]` could not be verified to be using a non-negative index. The proof would go through if one adds `invariant 0 <= k` to the loop. A simpler way to make the proof go through is if `k` can be inferred to have the subset type `nat`, in which case the non-negative index property follows directly from the types.

Once names have been resolved and pre-types inferred, the type system converts the pre-types into types and then goes into a phase of _adjusting_ those types into types that involve subset types. For example, if a local variable `x` (without a user-supplied type) is inferred to have pre-type `int` and all assignments to `x` are from variables declared to have `nat`, then `x` will, at the end of the type adjustment phase, have type `nat`.

## Resolution phases

Resolution proceeds in a number of phases. One group of these phases is called "pass 0" in the resolver (search for "`Pass 0`" in `ModuleResolver.cs`). This document is concerned with describe the phases in pass 0.

The name "pass 0" is somewhat arbitrary, since resolution performs some important tasks before pass 0. Those initial tasks are quite delicate, since they don't even have pre-types available. It would be good to have a document that describes those initial tasks. For now, suffice it to mention three ingredients of those tasks (performed in the order here listed):

* Resolve import relations between modules. This allows the rest of resolution to happen one module at a time. Indeed, the resolution phases described here at all performed for one module at a time (from inner modules to outer modules).
* Register the names of top-level declarations and member declarations in each module (that is, build a symbol table from names to declarations).
* Resolve the types that occur in top-level declarations and member declarations. (Note, `newtype`, subset type, and `const` declarations are allowed to omit types in their signatures. Such types will be inferred in pass 0. This issue is tricky, since it means that pass 0 can't rely on all type signatures to be known. More about that below.)

After pass 0, the resolver has many more phases. Those are grouped into pass 1, 2, and 3. The division between those names is rather arbitrary, but it generally true that later phases have more information about the module being resolved. As Dafny evolves and new phases are added, it is therefore a good idea to add new phases as late as possible, since that means they have more information to start with.

For the new type system, pass 0 consists of the following phases:

* Resolve names and infer pre-types. Ostensibly, this iterates over all declarations (in the module being resolved), computing the pre-type signature and body of each declaration. When one declaration uses another (that is, when one declaration has a name that resolves to another declaration), then it is only the pre-type signature of the other declaration that is needed. Because `newtype`, subset type, and `const` declarations can omit their type signatures and let them be inferred, the order in which declarations have to visited cannot be _a priori_ determined (in particular, note that determining such an order requires names to be resolved, but this is the phase that resolves names!). Therefore, this phase keeps track of which declarations are in progress and which have finished, and so will visit the declarations on demand. If any cycles are detected, they are reported as errors.

* Look for any under-specified pre-types, that is, places where pre-type inference did not come up with a type. This phase also fills in some additional information in the AST, like the `.ResolvedOp` field of binary expressions.

* Convert pre-types to types.

    The central operation in this phase is the `Combine` method, which combines whatever portions of the type may have been given explicitly in the program with the portions of the type inferred as a pre-type. In some cases, the pre-type may have more information; for example, when a local variable is declared without any type information. In other cases, the user-declared type may have more information; for example, if a variable is declared to have type `nat`, in which case pre-type inference would only have used the fact that this type has a pre-type of `int`. There are also cases where the two need to be combined; for example, with a declaration `class C<X>` in scope, the program may have declared a local variable `var c: C;` (where `C` is the subset type based on the nullable (pre-)type `C?`) and pre-type inference may have come up with `C?<int>`, so these will be combined into something that has both the subset type `C` and the type argument `int`.

    Whenever this combination reaches a place where no user-supplied type is given, `Combine` will output an _adjustable type_. This will let the later type-adjustment phase change the type to take subset types into consideration. Such an adjustable type is a wrapper around another type, which is the "current approximation" of that type. At first, that approximation is a "bottom type" (see description below of the type-adjustment phase), which will be gradually adjusted in the next phase.

    The bottom type is also a kind of wrapper, since it keeps track of the base type for which it is a bottom type. At the moment, both the adjustable-type wrapper and the bottom-type wrapper are implemented as type proxies (that is, as subclasses of `TypeProxy`). This may not be the best representation. It means that the type-adjustment phase needs its own version of `.Normalize()`, or otherwise one would skip passed these two special wrappers, too. It also means that the `.Type` getter of `Expression` needs to have an `.UnnormalizedType` variation, since `.Type` (anticipates uses that occur after type inference and) normalizes the types it gets and sets. A property of these wrappers is that a bottom-type wrapper is only ever used as the type contained in an adjustable-type wrapper.

    This phase needs to start by processing `newtype`, subset type, and `const` declarations, because their type signatures are needed when converting other types. This may seem like the dependency issues that during pre-type inference necessitated an on-demand computation. Luckily, this phase is simpler, because all it needs to do is to combine any user-supplied type in the signatures of these declarations with any inferred pre-type. This `Combine` operation does not need to look at any other declarations. So, all that is needed in this phase is to process those three kinds of declarations first, and then process all the other declarations.

* Adjust the initial user-supplied-type/inferred-pre-type combinations into types that take subset types into consideration.

## Conversions of pre-types into types, and type adjustments

Subset types form a hierarchy (a tree) rooted at a base type. Each subset type is declared with a predicate, but those predicates are not consulted during type adjustment. Instead, only the edges in the hierarchy are used. In other words, subset-type inference is done _nominally_, not semantically. For the purposes of type adjustments, we also use a "bottom type" for each base type. This bottom type is considered to be a subset of the base type and all its (transitive) subset types.

This phase sets up "flows", where one or several types have an influence on another type. For example, there is a flow from the RHS of an assignment to the LHS of the assignment, and there is a flow from the `then` and `else` expressions of an `if-then-else` expression into the result of the expression. This phase defines a set of such flows for the module. The `Solve()` method then finds the more general types that satisfy these flows.

The conversion from pre-types to types is coupled with the type-adjustment phase. The former needs to create adjustable types for the latter to adjust. Also, if there is a type that will not be adjusted, then the conversion phase should not set it to be a bottom type. For example, if the pre-types of expressions `x` and `y` are `int`, then the type of expression `x + y` is fixed to be `int`. That is, even if the types of `x` and `y` are eventually adjusted to, say, `nat`, the type of `x + y` is still defined to be `int`. For this situation, the type-adjustment phase does not define any flow from `x` and `y` to `x + y`, since it is not desirable to further adjust the type of `x + y`.

## Solving constraints

Pre-type inference builds up constraints that are required to hold among the pre-types to be inferred, and the type-adjustment phase builds up flows that are used to compute the final types as fix-points. At the moment, the data structures used in those phases are simple lists. Surely, there are far better ways to organize these constraints and flows. These can be improved and suitably optimized in the future.

In the current implementation, pre-type constraints are built up and solved for each declaration, whereas the flows are built up and solved for the entire module. The flows in one declaration do not affect the flows of other declarations, so the flows could be changed to be solved after each declaration (and doing so would probably be more efficient, since it a set of smaller fix points would be faster to compute than one fix point for the whole module).

Saying that pre-type constraints built up and then solved for each declaration is an over-simplification. In more detail, some parts of a declaration may be considered separately. For example, each attribute of a top-level declaration is considered separately. Moreover, pre-type inference sometimes _partially solves_ the constraints while building up more constraints. This currently happens in a few places, typified by member lookup, where pre-type inference will partially solve constraints in order to obtain enough of the type of `o` in an expression `o.f` before continuing to process the expression. If the partial solving does not yield enough of a pre-type for `o` to determine `f`, then an error is reported right away, rather than waiting until all constraints are solved. This design is a left-over from the old type system. The new type system has a notion of "guarded constraints", which could be used to eliminate any partial solving and instead just do solving at the end. However, in order to reduce changes between the old and new type system, it seemed wise to keep this design for now. Once the new type system is stable, it can be changed to use "guarded constraints" for expressions like member lookup, which will then admit strictly more programs.

## Debugging

The `/ntitrace:1` flag (for "New Type Inference TRACE") spills out information from pre-type inference and from type adjustment.
