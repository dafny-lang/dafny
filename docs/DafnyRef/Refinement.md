# 10. Refinement {#sec-module-refinement}

Refinement is the process of replacing something somewhat abstract with something somewhat more concrete.
For example, in one module one might declare a type name, with no definition,
such as `type T`, and then in a refining module, provide a definition.
One could prove general properties about the contents of an (abstract) module,
and use that abstract module, and then later provide a more concrete implementation without having to redo all of the proofs.

Dafny supports _module refinement_, where one module is created from another,
and in that process the new module may be made more concrete than the previous.
More precisely, refinement takes the following form in Dafny. One module
declares some program entities. A second module _refines_ the first by
declaring how to augment or replace (some of) those program entities.
The first module is called the _refinement parent_; the second is the
_refining_ module; the result of combining the two (the original declarations
and the augmentation directives) is the _assembled_ module or _refinement result_.

Syntactically, the refinement parent is a normal module declaration.
The refining module declares which module is its refinement parent with the
`refines` clause:
<!-- %check-resolve -->
```dafny
module P { // refinement parent
}
module M refines P { // refining module
}
```

The refinement result is created as follows.

0) The refinement result is a module within the same enclosing module as the
refining module, has the same name, and in fact replaces the refining module in their shared scope.

1) All the declarations (including import and export declarations) of the parent are copied into the refinement result.
These declarations are _not_ re-resolved. That is, the assignment of
declarations and types to syntactic names is not changed. The refinement
result may exist in a different enclosing module and with a different set of
imports than the refinement parent, so that if names were reresolved, the
result might be different (and possibly not semantically valid).
This is why Dafny does not re-resolve the names in their new context.

2) All the declarations of the refining module that have different names
than the declarations in the refinement parent are also copied into the
refinement result.
However, because the refining module is just a set of augmentation
directives and may refer to names copied from the refinement parent,
resolution of names and types of the declarations copied in this step is
performed in the context of the full refinement result.

3) Where declarations in the parent and refinement module have the same name,
the second refines the first and the combination, a refined declaration, is
the result placed in the refinement result module, to the exclusion of the
declarations with the same name from the parent and refinement modules.

The way the refinement result declarations are assembled depends on the kind of declaration;
the rules are described in subsections below.

So that it is clear that refinement is taking place, refining declarations
have some syntactic indicator that they are refining some parent declaration.
Typically this is the presence of a `...` token.

## 10.1. Export set declarations

A refining export set declaration begins with [the syntax](#g-module-export)
````grammar
"export" Ident ellipsis
````
but otherwise contains the same `provides`, `reveals` and `extends` sections,
with the ellipsis indicating that it is a refining declaration.

The result declaration has the same name as the two input declarations and the unions of names from each of the `provides`, `reveals`, and `extends`
sections, respectively.

An unnamed export set declaration from the parent is copied into the result
module with the name of the parent module. The result module has a default
export set according to the general rules for export sets, after all of
the result module's export set declarations have been assembled.

## 10.2. Import declarations

Aliasing import declarations are not refined. The result module contains the union
of the import declarations from the two input modules.
There must be no names in common among them.

Abstract import declarations (declared with `:` instead of `=`, [Section 4.6](#sec-module-abstraction)) are refined. The refinement parent contains the
abstract import and the refining module contains a regular aliasing
import for the same name. Dafny checks that the refining import _adheres_ to
the abstract import.

## 10.3. Sub-module declarations

With respect to refinement, a nested module behaves just like a top-level module. It may be declared abstract and it may be declared to `refine` some refinement parent. If the nested module is not refining anything and not being refined, then it is copied into the refinement result like any other declaration.

Here is some example code:
<!-- %check-verify -->
```dafny
abstract module P {
  module A { const i := 5 }
  abstract module B { type T }
}

module X refines P {
  module B' refines P.B { type T = int }
  module C { const k := 6}
}

module M {
  import X
  method m() {
    var z: X.B'.T := X.A.i + X.C.k;
  }
}
```
The refinement result of `P` and `X` contains nested modules `A`, `B'`, and `C`. It is this refinement result that is imported into `M`.
Hence the names `X.B'.T`, `X.A.i` and `X.C.k` are all valid.

## 10.4. Const declarations

Const declarations can be refined as in the following example.

<!-- %check-verify -->
```dafny
module A {
  const ToDefine: int
  const ToDefineWithoutType: int
  const ToGhost: int := 1
}

module B refines A {
  const ToDefine: int := 2
  const ToDefineWithoutType ... := 3
  ghost const ToGhost: int
  const NewConst: int
}
```

Formally, a child `const` declaration may refine a `const` declaration
from a parent module if

* the parent has no initialization,
* the child has the same type as the parent, and
* one or both of the following holds:
   * the child has an initializing expression
   * the child is declared `ghost` and the parent is not `ghost`.

A refining module can also introduce new `const` declarations that do
not exist in the refinement parent.

## 10.5. Method declarations

Method declarations can be refined as in the following example.

<!-- %check-verify -->
```dafny
module A {
  method ToImplement(x: int) returns (r: int)
    ensures r > x

  method ToStrengthen(x: int) returns (r: int)

  method ToDeterminize(x: int) returns (r: int)
    ensures r >= x
  {
    var y :| y >= x;
    return y;
  }

}

module B refines A {
  method ToImplement(x: int) returns (r: int)
  {
    return x + 2;
  }

  method ToStrengthen ...
    ensures r == x*2
  {
    return x*2;
  }

  method ToDeterminize(x: int) returns (r: int)
  {
    return x;
  }
}
```

Formally, a child `method` definition may refine a parent `method`
declaration or definition by performing one or more of the following
operations:

* provide a body missing in the parent (as in `ToDefine`),
* strengthen the postcondition of the parent method by adding one or more
  `ensures` clauses (as in `ToStrengthen`),
* provide a more deterministic version of a non-deterministic parent
  body (as in `ToDeterminize`), or

The type signature of a child method must be the same as that of the
parent method it refines. This can be ensured by providing an explicit
type signature equivalent to that of the parent (with renaming of
parameters allowed) or by using an ellipsis (`...`) to indicate copying
of the parent type signature. The body of a child method must satisfy
any ensures clauses from its parent in addition to any it adds.

A refined method is allowed only if it does not invalidate any parent
lemmas that mention it.

A refining module can also introduce new `method` declarations or
definitions that do not exist in the refinement parent.

## 10.6. Lemma declarations

As lemmas are (ghost) methods, the description of method refinement from
the previous section also applies to lemma refinement.

A valid refinement is one that does not invalidate any proofs. A lemma
from a refinement parent must still be valid for the refinement result
of any method or lemma it mentions.

## 10.7. Function and predicate declarations

Function (and equivalently predicate) declarations can be refined as in
the following example.

<!-- %check-verify -->
```dafny
module A {
  function F(x: int): (r: int)
    ensures r > x

  function G(x: int): (r: int)
    ensures r > x
  { x + 1 }
}

module B refines A {
  function F ...
  { x + 1 }

  function G ...
    ensures r == x + 1
}
```

Formally, a child `function` (or `predicate`) definition can refine a
parent `function` (or `predicate`) declaration or definition to

* provide a body missing in the parent,
* strengthen the postcondition of the parent function by adding one or more
  `ensures` clauses.

The relation between the type signature of the parent and child function
is the same as for methods and lemmas, as described in the previous section.

A refining module can also introduce new `function` declarations or
definitions that do not exist in the refinement parent.


## 10.8. Class, trait and iterator declarations

Class, trait, and iterator declarations are refined as follows: 
- If a class (or trait or iterator, respectively) `C` in a refining parent contains a
member that is not matched by a same-named member in the class `C` in the refining module, or vice-versa, then that class is copied as is to the 
refinement result.
- When there are members with the same name in the class in the refinement parent and in the refining module, then the combination occurs 
according to the rules for that category of member.

Here is an example code snippet:
<!-- %check-verify -->
```dafny
abstract module P {
  class C {
    function F(): int
      ensures F() > 0
  }
}

module X refines P {
  class C ... {
    function F...
      ensures F() > 0
    { 1 }
  }
}
```

## 10.9. Type declarations

Types can be refined in two ways:

- Turning an opaque type into a concrete type;
- Adding members to a datatype or a newtype.

For example, consider the following abstract module:

<!-- %check-verify -->
```dafny
abstract module Parent {
  type T
  type B = bool
  type S = s: string | |s| > 0 witness "!"
  newtype Pos = n: nat | n > 0 witness 1
  datatype Bool = True | False
}
``` <!-- %save Parent.tmp -->

In this module, type `T` is opaque and hence can be refined with any type,
including class types.  Types `B`, `S`, `Pos`, and `Bool` are concrete and
cannot be refined further, except (for `Pos` and `Bool`) by giving them
additional members or attributes (or refining their existing members, if any).
Hence, the following are valid refinements:

<!-- %check-verify %use Parent.tmp -->
```dafny
module ChildWithTrait refines Parent {
  trait T {}
}

module ChildWithClass refines Parent {
  class T {}
}

module ChildWithSynonymType refines Parent {
  type T = bool
}

module ChildWithSubsetType refines Parent {
  type T = s: seq<int> | s != [] witness [0]
}

module ChildWithDataType refines Parent {
  datatype T = True | False
}

abstract module ChildWithExtraMembers refines Parent {
  newtype Pos ... {
    method Print() { print this; }
  }

  datatype Bool ... {
    function AsDafnyBool() : bool { this.True? }
  }
}
```

(The last example is marked `abstract` because it leaves `T` opaque.)

Note that datatype constructors, codatatype destructors, and newtype definitions
cannot be refined: it is not possible to add or remove `datatype` constructors,
nor to change destructors of a `codatatype`, nor to change the base
type, constraint, or witness of a `newtype`.

When a type takes arguments, its refinement must use the same type arguments
with the same type constraints and the same variance.
 
When a type has type constraints, these type constraints must be preserved by
refinement.  This means that a type declaration `type T(!new)` cannot be refined
by a `class T`, for example. Similarly, a `type T(00)` cannot be refined by a
subset type with a `witness *` clause.

The refinement of an opaque type with body-less members can include both a definition
for the type along with a body for the member, as in this example:
<!-- %check-verify -->
```dafny
abstract module P {
  type T3 {
    function ToString(): string
  }
}

module X refines P {
  newtype T3 = i | 0 <= i < 10 {
    function ToString... { "" }
  }
}
```

Note that type refinements are not required to include the `...` indicator that they are refining a parent type.

## 10.10. Statements

The refinement syntax (`...`) in statements is deprecated.

