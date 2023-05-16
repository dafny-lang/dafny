# 4. Modules ([grammar](#g-module)) {#sec-modules}

Examples:
<!-- %no-check -->
```dafny
module N  { }
import A
export A reveals f
```

Structuring a program by breaking it into parts is an important part of
creating large programs. In Dafny, this is accomplished via _modules_.
Modules provide a way to group together related types, classes, methods,
functions, and other modules, as well as to control the scope of
declarations. Modules may import each other for code reuse, and it is
possible to abstract over modules to separate an implementation from an
interface.

Module declarations are of three types:
- a module definition
- a module import
- a module export definition

Module definitions and imports each declare a submodule
of its enclosing module, which may be the
implicit, undeclared, top-level module. 

## 4.1. Declaring New Modules ([grammar](#g-module-definition)) {#sec-module-definition}

Examples:
<!-- %check-resolve -->
```dafny
module P { const i: int }
abstract module A.Q { method m() {} }
module M { module N { } }
```

A _module definition_
- has an optional modifier (only `abstract` is allowed)
- followed by the keyword "module"
- followed by a name (a sequence of dot-separated identifiers)
- followed by a body enclosed in curly braces

A module body consists of any declarations that are allowed at the top
level: classes, datatypes, types, methods, functions, etc.

<!-- %check-resolve -->
```dafny
module Mod {
  class C {
    var f: int
    method m()
  }
  datatype Option = A(int) | B(int)
  type T
  method m()
  function f(): int
}
```

You can also put a module inside another, in a nested fashion:

<!-- %check-resolve -->
```dafny
module Mod {
  module Helpers {
    class C {
      method doIt()
      var f: int
    }
  }
}
```

Then you can refer to the members of the `Helpers` module within the
`Mod` module by prefixing them with "Helpers.". For example:

<!-- %check-resolve -->
```dafny
module Mod {
  module Helpers {
    class C {
      constructor () { f := 0; }
      method doIt()
      var f: int
    }
  }
  method m() {
    var x := new Helpers.C();
    x.doIt();
    x.f := 4;
  }
}
```

Methods and functions defined at the module level are available like
classes, with just the module name prefixing them. They are also
available in the methods and functions of the classes in the same
module.

<!-- %check-resolve -->
```dafny
module Mod {
  module Helpers {
    function addOne(n: nat): nat {
      n + 1
    }
  }
  method m() {
    var x := 5;
    x := Helpers.addOne(x); // x is now 6
  }
}
```

Note that everything declared at the top-level
(in all the files constituting the program) is implicitly part
of a single implicit unnamed global module.

## 4.2. Declaring nested modules standalone

As described in the previous section, module declarations can be nested.
It is also permitted to declare a nested module _outside_ of its
"containing" module. So instead of
<!-- %check-resolve -->
```dafny
module A {
  module B {
  }
}
```
one can write
<!-- %check-resolve -->
```dafny
module A {
}
module A.B {
}
```
The second module is completely separate; for example, it can be in
a different file.
This feature provides flexibility in writing and maintenance;
for example, it can reduce the size of module `A` by extracting module `A.B`
into a separate body of text.

However, it can also lead to confusion, and program authors need to take care.
It may not be apparent to a reader of module `A` that module `A.B` exists;
the existence of `A.B` might cause names to be resolved differently and
the semantics of the program might be (silently) different if `A.B` is
present or absent.

## 4.3. Importing Modules ([grammar](#g-module-import)) {#sec-importing-modules}

Examples:
<!-- %no-check -->
```dafny
import A
import opened B
import A = B
import A : B
import A.B
import A`E
import X = A.B`{E,F}
```

Sometimes you want to refer to
things from an existing module, such as a library. In this case, you
can _import_ one module into another. This is done via the `import`
keyword, which has two forms with different meanings.
The simplest form is the concrete import, which has
the form `import A = B`. This declaration creates a reference to the
module `B` (which must already exist), and binds it to the new local name
`A`. This form can also be used to create a reference to a nested
module, as in `import A = B.C`. The other form, using a `:`, is
described in [Section 4.6](#sec-module-abstraction).

As modules in the same scope must have different names, this ability
to bind a module to a new name allows disambiguating separately developed
external modules that have the same name.
Note that the new name is only bound in the scope containing
the import declaration; it does not create a global alias. For
example, if `Helpers` was defined outside of `Mod`, then we could import
it:

<!-- %check-verify -->
```dafny
module Helpers {
  function addOne(n: nat): nat {
    n + 1
  }
}
module Mod {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6;
  }
}
```

Note that inside `m()`, we have to use `A` instead of `Helpers`, as we bound
it to a different name. The name `Helpers` is not available inside `m()` (or anywhere else inside `Mod`),
as only names that have been bound inside `Mod` are available. In order
to use the members from another module, that other module either has to be declared
there with `module` or imported with `import`. (As described below, the
resolution of the `ModuleQualifiedName` that follows the `=` in the `import`
statement or the `refines` in a module declaration uses slightly
different rules.)

We don't have to give `Helpers` a new name, though, if we don't want
to. We can write `import Helpers = Helpers` to import the module under
its own name; Dafny
even provides the shorthand `import Helpers` for this behavior. You
can't bind two modules with the same name at the same time, so
sometimes you have to use the = version to ensure the names do not
clash. When importing nested modules, `import B.C` means `import C = B.C`;
the implicit name is always the last name segment of the module designation.

The first identifier in the dot-separated sequence of identifers that constitute
the qualified name of the module being imported is resolved as (in order)
- a submodule of the importing module, 
- or a sibling module of the importing module, 
- or a sibling module of some containing module, traversing outward. 
There is no way to refer to a containing module, only
sibling modules (and their submodules).

Import statements may occur at the top-level of a program
(that is, in the implicit top-level module of the program) as well.
There they serve as a way to give a new name, perhaps a
shorthand name, to a module. For example,

<!-- %check-resolve Modules.1.expect -->
```dafny
module MyModule { } // declare MyModule
import MyModule  // error: cannot add a module named MyModule
                 // because there already is one
import M = MyModule // OK. M and MyModule are equivalent
```

## 4.4. Opening Modules {#sec-opening-modules}

Sometimes, prefixing the members of the module you imported with its
name is tedious and ugly, even if you select a short name when
importing it. In this case, you can import the module as `opened`,
which causes all of its members to be available without adding the
module name. The `opened` keyword, if present, must immediately follow `import`.
For example, we could write the previous example as:

<!-- %check-verify -->
```dafny
module Helpers {
  function addOne(n: nat): nat {
    n + 1
  }
}
module Mod {
  import opened Helpers
  method m() {
    assert addOne(5) == 6;
  }
}
```

When opening modules, the newly bound members have lower priority
than local definitions. This means if you define
a local function called `addOne`, the function from `Helpers` will no
longer be available under that name. When modules are opened, the
original name binding is still present however, so you can always use
the name that was bound to get to anything that is hidden.

<!-- %check-verify Modules.2.expect -->
```dafny
module Helpers {
  function addOne(n: nat): nat {
    n + 1
  }
}
module Mod {
  import opened H = Helpers
  function addOne(n: nat): nat {
    n - 1
  }
  method m() {
    assert addOne(5) == 6; // this is now false,
                           // as this is the function just defined
    assert H.addOne(5) == 6; // this is still true
  }
}
```

If you open two modules that both declare members with the same name,
then neither member can be referred to without a module prefix, as it
would be ambiguous which one was meant. Just opening the two modules
is not an error, however, as long as you don't attempt to use members
with common names. However, if the ambiguous references actually
refer to the same declaration, then they are permitted.
The `opened` keyword may be used with any kind of
`import` declaration, including the module abstraction form.

An `import opened` may occur at the top-level as well. For example,
<!-- %check-resolve -->
```dafny
module MyModule {  } // declares MyModule
import opened MyModule // does not declare a new module, but does
                       // make all names in MyModule available in
                       // the current scope, without needing
                       // qualification
import opened M = MyModule // names in MyModule are available in
                       // the current scope without qualification
                       // or qualified with either M (because of this
                       // import) or MyModule (because of the original
                       // module definition)
```

The Dafny style guidelines suggest using opened imports sparingly.
They are best used when the names being imported have obvious
and unambiguous meanings and when using qualified names would be
verbose enough to impede understanding.

There is a special case in which the behavior described above is altered.
If a module `M` declares a type `M` and `M` is `import opened` without renaming inside 
another module `X`, then the rules above would have, within `X`,
`M` mean the module and `M.M` mean the type. This is verbose. So in this 
somewhat common case, the type `M` is effectively made a local declaration within `X`
so that it has precedence over the module name. Now `M` refers to the type.
If one needs to refer to the module, it will have to be renamed as part of
the `import opened` statement.	

This special-case behavior does give rise to a source of ambiguity. Consider
the example
<!-- %check-resolve Modules.3.expect -->
```dafny
module Option {
  const a := 1
  datatype Option = A|B { static const a := 2 }
}

module X {
  import opened Option
  method M() { print Option.a; }
}
```
`Option.a` now means the `a` in the datatype instead of the `a` in the module.
To avoid confusion in such cases, it is an ambiguity error if a name
that is declared in both the datatype and the module is used
when there is an `import open` of
the module (without renaming).

## 4.5. Export Sets and Access Control ([grammar](#g-module-export)) {#sec-export-sets}

Examples:
<!-- %no-check -->
```dafny
export E extends F reveals f,g provides g,h
export E reveals *
export reveals f
export E
export
export E ... reveals f
```

In some programming languages, keywords such as `public`, `private`, and `protected`
are used to control access to (that is, visibility of) declared program entities.
In Dafny, modules and export sets provide that capability.
Modules combine declarations into logically related groups.
Export sets then permit selectively exposing subsets of a module's declarations;
another module can import the export set appropriate to its needs.
A user can define as many export sets as are needed to provide different
kinds of access to the module's declarations.
Each export set designates a list of names, which must be
names that are declared in the module (or in a refinement parent).

By default (in the absence of any export set declarations)
all the names declared in a module are available outside the
module using the `import` mechanism.
An _export set_ enables a module to disallow the
use of some declarations outside the module.

Export sets have names; those names are used in `import` statements to
designate which export set of a module is being imported.
If a module `M` has export sets
`E1` and `E2`, we can write ``import A = M`E1`` to create a module alias
`A` that contains only the
names in `E1`. Or we can write ``import A = M`{E1,E2}`` to import the union
of names in `E1` and `E2` as module alias `A`.
As before, ``import M`E1`` is an
abbreviation of ``import M = M`E1``.

If no export set is given in an import
statement, the default export set of the module is used.

 There are various
defaults that apply differently in different cases.
The following description is with respect to an example module `M`:

_`M` has no export sets declared_. Then another module may simply `import Z = M`
to obtain access to all of M's declarations.

_`M` has one or more named export sets (e.g., `E`, `F`)_. Then another module can
write ``import Z = M`E`` or ``import Z = M`{E,F}`` to obtain access to the
names that are listed in export set `E` or to the union of those in export sets
`E` and `F`, respectively. If no export set has the same name as the module,
then an export set designator must be used: in that case you cannot write
simply ``import Z = M``.

_`M` has an unnamed export set, along with other export sets (e.g., named `E`)_. The unnamed
export set is the default export set and implicitly has the same name as
the module. Because there is a default export set, another module may write
either ``import Z = M`` or ``import Z = M`M`` to import the names in that
default export set. You can also still use the other export sets with the
explicit designator: ``import Z = M`E``

_`M` declares an export set with the same name as the module_. This is equivalent
to declaring an export set without a name. ``import M`` and ``import M`M``
perform the same function in either case; the export set with or without
the name of the module is the default export set for the module.

Note that names of module aliases (declared by import statements) are
just like other names in a module; they can be included or omitted from
export sets.
Names brought into a module by [_refinement_](#sec-module-refinement) are treated the same as
locally declared names and can be listed in export set declarations.
However, names brought into a module by `import opened` (either into a module
or a refinement parent of a module) may
not be further exported. For example,
<!-- %check-verify -->
```dafny
module A {
  const a := 10;
  const z := 10;
}
module B {
  import opened Z = A // includes a, declares Z
  const b := Z.a; // OK
}
module C {
  import opened B // includes b, Z, but not a
  method m() {
    //assert b == a; // error: a is not known
    //assert b == B.a; // error: B.a is not valid
    //assert b == A.a; // error: A is not known
    assert b == Z.a; // OK: module Z is known and includes a
  }
}
```

However, in the above example,

* if `A` has one export set `export Y reveals a`
then the import in module `B` is invalid because `A` has no default
export set;
* if `A` has one export set `export Y reveals a` and `B` has ``import Z = A`Y``
then `B`'s import is OK. So is the use of `Z.a` in the assert because `B`
declares `Z` and `C` brings in `Z` through the `import opened` and
`Z` contains `a` by virtue of its declaration. (The alias `Z` is not able to
have export sets; all of its names are visible.)
* if `A` has one export set `export provides z` then `A` does have a
default export set, so the import in `B` is OK, but neither the use of `a`
in `B` nor as `Z.a` in C would be valid, because `a` is not in `Z`.

The default export set is important in the resolution of qualified
names, as described in [Section 4.8](#sec-name-resolution).

There are a few unusual cases to be noted:
- an export set can be completely empty, as in `export Nothing`
- an eponymous export set can be completely empty, as in `export`, which by default has the same name as the enclosing module; this is a way to make the module completely private
- an export set declaration followed by an extreme predicate declaration looks like this:
`export least predicate P() { true }`
In this case, the `least` (or `greatest`) is the identifier naming the export set.
Consequently, `export least predicate P[nat]() { true }` is illegal because `[nat]` cannot be part of a non-extreme predicate.
So, it is not possible to declare an eponymous, empty export set by omitting the export id immediately prior to a declaration of an extreme predicate,
because the `least` or `greatest` token is parsed as the export set identifier. The workaround for this situation is to 
either put the name of the module in explicitly as the export ID (not leaving it to the default) or reorder the declarations.
- To avoid confusion, the code
<!-- %check-verify-warn Modules.10.expect -->
```dafny
module M {
  export
  least predicate P() { true }
}
```
provokes a warning telling the user that the `least` goes with the `export`.

### 4.5.1. Provided and revealed names {#sec-provided-and-revealed-names}

Names can be exported from modules in two ways, designated by `provides`
and `reveals` in the export set declaration.

When a name is exported as _provided_, then inside a module that has
imported the name only the name is known, not the details of the
name's declaration.

For example, in the following code the constant `a` is exported as provided.
<!-- %check-verify Modules.4.expect -->
```dafny
module A {
  export provides a
  const a := 10;
  const b := 20;
}

module B {
  import A
  method m() {
    assert A.a == 10; // a is known, but not its value
    // assert A.b == 20; // b is not known through A`A
  }
}
```
Since `a` is imported into module `B` through the default export set ``A`A``,
it can be referenced in the assert statement. The constant `b` is not
exported, so it is not available. But the assert about `a` is not provable
because the value of `a` is not known in module `B`.

In contrast, if `a` is exported as _revealed_, as shown in the next example,
its value is known and the assertion can be proved.
<!-- %check-verify -->
```dafny
module A {
  export reveals a
  const a := 10;
  const b := 20;
}

module B {
  import A
  method m() {
    assert A.a == 10; // a and its value are known
    // assert A.b == 20; // b is not known through A`A
  }
}
```

The following table shows which parts of a declaration are exported by an
export set that `provides` or `reveals` the declaration.

```text
 declaration         | what is exported    | what is exported
                     | with provides       | with reveals
---------------------|---------------------|---------------------
 const x: X := E     | const x: X          | const x: X := E
---------------------|---------------------|---------------------
 var x: X            | var x: X            | not allowed
---------------------|---------------------|---------------------
 function F(x: X): Y | function F(x: X): Y | function F(x: X): Y
   specification...  |   specification...  |   specification...
 {                   |                     | {
   Body              |                     |   Body
 }                   |                     | }
---------------------|---------------------|---------------------
 method M(x: X)      | method M(x: X)      | not allowed
   returns (y: Y)    |   returns (y: Y)    |
   specification...  |   specification...  |
 {                   |                     |
   Body;             |                     |
 }                   |                     |
---------------------|---------------------|---------------------
 type Opaque         | type Opaque         | type Opaque
 {                   |                     |
   // members...     |                     |
 }                   |                     |
---------------------|---------------------|---------------------
 type Synonym = T    | type Synonym        | type Synonym = T
---------------------|---------------------|---------------------
 type S = x: X       | type S              | type S = x: X
   | P witness E     |                     |   | P witness E
---------------------|---------------------|---------------------
 newtype N = x: X    | type N              | newtype N = x: X
   | P witness E     |                     |   | P witness E
 {                   |                     |
   // members...     |                     |
 }                   |                     |
```
```text
---------------------|---------------------|---------------------
 datatype D =        | type D              | datatype D =
     Ctor0(x0: X0)   |                     |    Ctor0(x0: X0)
   | Ctor1(x1: X1)   |                     |  | Ctor1(x1: X1)
   | ...             |                     |  | ...
 {                   |                     |
   // members...     |                     |
 }                   |                     |
---------------------|---------------------|---------------------
 class Cl            | type Cl             | class Cl
   extends T0, ...   |                     |   extends T0, ...
 {                   |                     | {
   constructor ()    |                     |   constructor ()
     spec...         |                     |     spec...
   {                 |                     |
     Body;           |                     |
   }                 |                     |
   // members...     |                     |
 }                   |                     | }
---------------------|---------------------|---------------------
 trait Tr            | type Tr             | trait Tr
   extends T0, ...   |                     |   extends T0, ...
 {                   |                     |
   // members...     |                     |
 }                   |                     |
---------------------|---------------------|---------------------
 iterator Iter(x: X) | type Iter           | iterator Iter(x: X)
   yields (y: Y)     |                     |   yields (y: Y)
   specification...  |                     |   specification...
 {                   |                     |
   Body;             |                     |
 }                   |                     |
---------------------|---------------------|---------------------
 module SubModule    | module SubModule    | not allowed
   ...               |   ...               |
 {                   | {                   |
   export SubModule  |   export SubModule  |
     ...             |     ...             |
   export A ...      |                     |
   // decls...       |   // decls...       |
 }                   | }                   |
---------------------|---------------------|---------------------
 import L = MS       | import L = MS       | not allowed
---------------------|---------------------|---------------------
```

Variations of functions (e.g., `predicate`, `twostate function`) are
handled like `function` above, and variations of methods (e.g.,
`lemma` and `twostate lemma`) are treated like `method` above. Since
the whole signature is exported, a function or method is exported to
be of the same kind, even through `provides`. For example, an exported
`twostate lemma` is exported as a `twostate lemma` (and thus is known
by importers to have two implicit heap parameters), and an exported
`least predicate P` is exported as a `least predicate P` (and thus
importers can use both `P` and its prefix predicate `P#`).

If `C` is a `class`, `trait`, or `iterator`, then `provides C` exports
the non-null reference type `C` as an opaque type. This does not reveal
that `C` is a reference type, nor does it export the nullable type `C?`.

In most cases, exporting a `class`, `trait`, `datatype`, `codatatype`, or
opaque type does not automatically export its members. Instead, any member
to be exported must be listed explicitly. For example, consider the type
declaration

<!-- %check-resolve -->
```dafny
trait Tr {
  function F(x: int): int { 10 }
  function G(x: int): int { 12 }
  function H(x: int): int { 14 }
}
```

An export set that contains only `reveals Tr` has the effect of exporting

<!-- %check-resolve -->
```dafny
trait Tr {
}
```

and an export set that contains only `provides Tr, Tr.F reveals Tr.H` has
the effect of exporting

<!-- %check-resolve -->
```dafny
type Tr {
  function F(x: int): int
  function H(x: int): int { 14 }
}
```

There is no syntax (for example, `Tr.*`) to export all members of a type.

Some members are exported automatically when the type is revealed.
Specifically:
- Revealing a `datatype` or `codatatype` automatically exports the type's
  discriminators and destructors.
- Revealing an `iterator` automatically exports the iterator's members.
- Revealing a class automatically exports the class's anonymous constructor, if any.

For a `class`, a `constructor` member can be exported only if the class is revealed.
For a `class` or `trait`, a `var` member can be exported only if the class or trait is revealed
(but a `const` member can be exported even if the enclosing class or trait is only provided).

When exporting a sub-module, only the sub-module's eponymous export set is exported.
There is no way for a parent module to export any other export set of a sub-module, unless
it is done via an `import` declaration of the parent module.

The effect of declaring an import as `opened` is confined to the importing module. That
is, the ability of use such imported names as unqualified is not passed on to further
imports, as the following example illustrates:

<!-- %check-resolve Modules.5.expect -->
```dafny
module Library {
  const xyz := 16
}

module M {
  export
    provides Lib
    provides xyz // error: 'xyz' is not declared locally

  import opened Lib = Library

  const k0 := Lib.xyz
  const k1 := xyz
}

module Client {
  import opened M

  const a0 := M.Lib.xyz
  const a1 := Lib.xyz
  const a2 := M.xyz // error: M does not have a declaration 'xyz'
  const a3 := xyz // error: unresolved identifier 'xyz'
}
```

As highlighted in this example, module `M` can use `xyz` as if it were a local
name (see declaration `k1`), but the unqualified name `xyz` is not made available
to importers of `M` (see declarations `a2` and `a3`), nor is it possible for
`M` to export the name `xyz`.

A few other notes:

* A `provides` list can mention `*`, which means that all local names
  (except export set names) in the module are exported as `provides`.
* A `reveals` list can mention `*`, which means that all local names
  (except export set names) in the module are exported as `reveals`, if
  the declaration is allowed to appear in a `reveals` clause, or as
  `provides`, if the declaration is not allowed to appear in a `reveals`
  clause.
* If no export sets are declared, then the implicit
  export set is `export reveals *`.
* A refinement module acquires all the export sets from its refinement parent.
* Names acquired by a module from its refinement parent are also subject to
  export lists. (These are local names just like those declared directly.)

### 4.5.2. Extends list {#sec-extends-list}
An export set declaration may include an _extends_ list, which is a list of
one or more export set names from the same module containing the declaration
(including export set names obtained from a refinement parent).
The effect is to include in the declaration the union of all the names in
the export sets in the extends list, along with any other names explicitly
included in the declaration. So for example in
<!-- %check-resolve -->
```dafny
module M {
  const a := 10;
  const b := 10;
  const c := 10;
  export A reveals a
  export B reveals b
  export C extends A, B
    reveals c
}
```
export set `C` will contain the names `a`, `b`, and `c`.

## 4.6. Module Abstraction {#sec-module-abstraction}

Sometimes, using a specific implementation is unnecessary; instead,
all that is needed is a module that implements some interface.  In
that case, you can use an _abstract_ module import. In Dafny, this is
written `import A : B`.  This means bind the name `A` as before, but
instead of getting the exact module `B`, you get any module which
_adheres_ to `B`.  Typically, the module `B` may have abstract type
definitions, classes with bodiless methods, or otherwise be unsuitable
to use directly.  Because of the way refinement is defined, any
refinement of `B` can be used safely. For example, suppose we start with
these declarations:

<!-- %check-verify -->
```dafny
abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
```

We can be more precise if we know that `addSome` actually adds
exactly one. The following module has this behavior. Further, the
postcondition is stronger, so this is actually a refinement of the
Interface module.

<!-- %check-verify -->
```dafny
module Implementation {
  function addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
```

We can then substitute `Implementation` for `A` in a new module, by
declaring a refinement of `Mod` which defines  `A` to be `Implementation`.

<!-- %check-build -->
```dafny
abstract module Interface {
  function addSome(n: nat): nat
    ensures addSome(n) > n
}
abstract module Mod {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}
module Implementation {
  function addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
module Mod2 refines Mod {
  import A = Implementation
  ...
}
```

When you refine an abstract import into a concrete one
Dafny checks that the concrete module is a
refinement of the abstract one. This means that the methods must have
compatible signatures, all the classes and datatypes with their
constructors and fields in the abstract one must be present in the
concrete one, the specifications must be compatible, etc.

A module that includes an abstract import must be declared `abstract`.

## 4.7. Module Ordering and Dependencies {#sec-module-ordering}

Dafny isn't particular about the textual order in which modules are
declared, but
they must follow some rules to be well formed. In particular,
there must be a way to order the modules in a program such that each
only refers to things defined **before** it in the ordering. That
doesn't mean the modules have to be given textually in that order in
the source text. Dafny will
figure out that order for you, assuming you haven't made any circular
references. For example, this is pretty clearly meaningless:

<!-- %check-resolve Modules.6.expect -->
```dafny
import A = B
import B = A // error: circular
```

You can have import statements at the toplevel and you can import
modules defined at the same level:

<!-- %check-verify -->
```dafny
import A = B
method m() {
  A.whatever();
}
module B { method whatever() {} }
```

In this case, everything is well defined because we can put `B` first,
followed by the `A` import, and then finally `m()`. If there is no
permitted ordering, then Dafny will give an error, complaining about a cyclic
dependency.

Note that when rearranging modules and imports, they have to be kept
in the same containing module, which disallows some pathological
module structures. Also, the imports and submodules are always
considered to be before their containing module, even at the toplevel. This means that the
following is not well formed:

<!-- %check-resolve Modules.7.expect -->
```dafny
method doIt() { }
module M {
  method m() {
    doIt(); // error: M precedes doIt
  }
}
```

because the module `M` must come before any other kind of members, such
as methods. To define global functions like this, you can put them in
a module (called `Globals`, say) and open it into any module that needs
its functionality. Finally, if you import via a path, such as `import A
= B.C`, then this creates a dependency of `A` on `B`, and `B` itself
depends on its own nested module `B.C`.

## 4.8. Name Resolution {#sec-name-resolution}

When Dafny sees something like `A<T>.B<U>.C<V>`, how does it know what each part
refers to? The process Dafny uses to determine what identifier
sequences like this refer to is name resolution. Though the rules may
seem complex, usually they do what you would expect. Dafny first looks
up the initial identifier. Depending on what the first identifier
refers to, the rest of the identifier is looked up in the appropriate
context.

In terms of the grammar, sequences like the above are represented as
a ``NameSegment`` followed by 0 or more ``Suffix``es.
The form shown above contains three instances of
``AugmentedDotSuffix_``.

The resolution is different depending on whether it is in
a module context, an expression context or a type context.

### 4.8.1. Modules and name spaces

A module is a collection of declarations, each of which has a name.
These names are held in two namespaces.

* The names of export sets
* The names of all other declarations, including submodules and aliased modules

In addition names can be classified as _local_ or _imported_.

* Local declarations of a module are the declarations
 that are explicit in the module and the
local declarations of the refinement parent. This includes, for
example, the `N` of `import N = ` in the refinement parent, recursively.
* Imported names of a module are those brought in by `import opened` plus
the imported names in the refinement parent.

Within each namespace, the local names are unique. Thus a module may
not reuse a name that a refinement parent has declared (unless it is a
refining declaration, which replaces both declarations, as described
in [Section 10](#sec-module-refinement)).

Local names take precedence over imported names. If a name is used more than
once among imported names (coming from different imports), then it is
ambiguous to _use_ the name without qualification.

### 4.8.2. Module Id Context Name Resolution

A qualified name may be used to refer to a module in an import statement or a refines clause of a module declaration.
Such a qualified name is resolved as follows, with respect to its syntactic
location within a module `Z`:

1. The leading identifier of the qualified name is resolved as a local or imported module name of `Z`, if there
is one with a matching name. The target of a `refines` clause does not
consider local names, that is, in `module Z refines A.B.C`, any contents of `Z`
are not considered in finding `A`.

2. Otherwise, it is resolved as a local or imported module name of the most enclosing module of `Z`,
   iterating outward to each successive enclosing module until a match is
found or the default toplevel module is reached without a match.
No consideration of export sets, default or otherwise, is used in this step.
However, if at any stage a matching name is found that is not a module
declaration, the resolution fails. See the examples below.

3a. Once the leading identifier is resolved as say module `M`, the next
   identifier in the quallified name
   is resolved as a local or imported module name within `M`.
   The resolution is restricted to the default export set of `M`.

3b. If the resolved module name is a module alias (from an `import` statement)
   then the target of the alias is resolved as a new qualified name
   with respect to its syntactic context (independent of any resolutions or
modules so far). Since `Z` depends on `M`, any such alias target will
already have been resolved, because modules are resolved in order of
dependency.

4. Step 3 is iterated for each identifier in the qualified module id,
   resulting in a module that is the final resolution of the complete
   qualified id.

Ordinarily a module must be _imported_ in order for its constituent
declarations to be visible inside a given module `M`. However, for the
resolution of qualified names this is not the case.

This example shows that the resolution of the refinement parent does not
use any local names:
<!-- %check-verify -->
```dafny
module A {
  const a := 10
}

module B refines A { // the top-level A, not the submodule A
  module A { const a := 30 }
  method m() { assert a == 10; } // true
}
```
In the example, the `A` in `refines A` refers to the global `A`, not the submodule `A`.


### 4.8.3. Expression Context Name Resolution

The leading identifier is resolved using the first following
rule that succeeds.

0. Local variables, parameters and bound variables. These are things like
   `x`, `y`, and `i` in `var x;, ... returns (y: int)`, and
   `forall i :: ....` The declaration chosen is the match from the
   innermost matching scope.

1. If in a class, try to match a member of the class. If the member that
   is found is not static an implicit `this` is inserted. This works for
   fields, functions, and methods of the current class (if in a static
   context, then only static methods and functions are allowed). You can
   refer to fields of the current class either as `this.f` or `f`,
   assuming of course that `f` is not hidden by one of the above. You
   can always prefix `this` if needed, which cannot be hidden. (Note that a
   field whose name is a string of digits must always have some prefix.)

2. If there is no ``Suffix``, then look for a datatype constructor, if
   unambiguous. Any datatypes that don't need qualification (so the
   datatype name itself doesn't need a prefix) and also have a uniquely
   named constructor can be referred to just by name.  So if
   `datatype List = Cons(List) | Nil` is the only datatype that declares
   `Cons` and `Nil` constructors, then you can write `Cons(Cons(Nil))`.
   If the constructor name is not unique, then you need to prefix it with
   the name of the datatype (for example `List.Cons(List.Nil)))`. This is
   done per constructor, not per datatype.

3. Look for a member of the enclosing module.

4. Module-level (static) functions and methods

In each module, names from opened modules are also potential matches, but
only after names declared in the module.
If an ambiguous name is found or a name of the wrong kind (e.g. a module
instead of an expression identifier), an error is generated, rather than continuing
down the list.

After the first identifier, the rules are basically the
same, except in the new context. For example, if the first identifier is
a module, then the next identifier looks into that module. Opened modules
only apply within the module it is opened into. When looking up into
another module, only things explicitly declared in that module are
considered.

To resolve expression `E.id`:

First resolve expression E and any type arguments.

* If `E` resolved to a module `M`:
  0. If `E.id<T>` is not followed by any further suffixes, look for
     unambiguous datatype constructor.
  1. Member of module M: a sub-module (including submodules of imports),
     class, datatype, etc.
  2. Static function or method.
* If `E` denotes a type:
  3. Look up id as a member of that type
* If `E` denotes an expression:
  4. Let T be the type of E. Look up id in T.

### 4.8.4. Type Context Name Resolution

In a type context the priority of identifier resolution is:

1. Type parameters.

2. Member of enclosing module (type name or the name of a module).

To resolve expression `E.id`:

* If `E` resolved to a module `M`:
  0. Member of module M: a sub-module (including submodules of imports),
     class, datatype, etc.
* If `E` denotes a type:
  1. Then the validity and meaning of `id` depends on the type and
     must be a user-declared or pre-defined member of the type.
