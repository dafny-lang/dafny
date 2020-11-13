# Modules

````grammar
SubModuleDecl = ( ModuleDefinition_ | ModuleImport_ )
````

Structuring a program by breaking it into parts is an important part of
creating large programs. In Dafny, this is accomplished via _modules_.
Modules provide a way to group together related types, classes, methods,
functions, and other modules, as well as to control the scope of
declarations. Modules may import each other for code reuse, and it is
possible to abstract over modules to separate an implementation from an
interface.

## Declaring New Modules
````grammar
ModuleDefinition_ = "module" { Attribute } ModuleName
        [ [  "exclusively" ] "refines" QualifiedModuleName ]
        "{" { TopDecl } "}"
QualifiedModuleName = Ident { "." Ident }
````
A `QualifiedModuleName` is a qualified name that is known to refer to a module;
a _qualified name_ is a sequence of `.`-separated identifiers, which designates
a program entity by representing increasingly-nested scopes.

A new module is declared with the `module` keyword, followed by the name
of the new module, and a pair of curly braces ({}) enclosing the body
of the module:

```dafny
module Mod {
  ...
}
```

A module body can consist of anything that you could put at the top
level. This includes classes, datatypes, types, methods, functions, etc.

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

```dafny
module Mod {
  module Helpers { ... }
  method m() {
    var x := new Helpers.C;
    x.doIt();
    x.f := 4;
  }
}
```

Methods and functions defined at the module level are available like
classes, with just the module name prefixing them. They are also
available in the methods and functions of the classes in the same
module.

```dafny
module Mod {
  module Helpers {
    function method addOne(n: nat): nat {
      n + 1
    }
  }
  method m() {
    var x := 5;
    x := Helpers.addOne(x); // x is now 6
  }
}
```

TO BE WRITTEN - standalone declaration of nested modules

Note that everything declared at the top-level
(in all the files constituting the program) is implicitly part
of a single implicit unnamed global module.

## Importing Modules
````grammar
ModuleImport_ = "import" ["opened" ] ModuleName
    [ "=" QualifiedModuleName
    | "as" QualifiedModuleName ["default" QualifiedModuleName ]
    ]
    [ ";" ]
````

Sometimes you want to refer to
things from an existing module, such as a library. In this case, you
can _import_ one module into another. This is done via the `import`
keyword, which has two forms with different meanings.
The simplest form is the concrete import, which has
the form `import A = B`. This declaration creates a reference to the
module `B` (which must already exist), and binds it to the new name
`A`. This form can also be used to create a reference to a nested
module, as in `import A = B.C`.

As modules in the same scope must have different names, this ability
to bind a module to a new name allows disambiguating separately developed
external modules that have the same name.
Note that the new name is only bound in the scope containing
the import declaration; it does not create a global alias. For
example, if `Helpers` was defined outside of `Mod`, then we could import
it:

```dafny
module Helpers {
  ...
}
module Mod {
  import A = Helpers
  method m() {
    assert A.addOne(5) == 6;
  }
}
```

Note that inside `m()`, we have to use `A` instead of `Helpers`, as we bound
it to a different name. The name `Helpers` is not available inside `m()`,
as only names that have been bound inside `Mod` are available. In order
to use the members from another module, that other module either has to be declared
there with `module` or imported with `import`.

We don't have to give `Helpers` a new name, though, if we don't want
to. We can write `import Helpers = Helpers` to import the module under
its own name; Dafny
even provides the shorthand `import Helpers` for this behavior. You
can't bind two modules with the same name at the same time, so
sometimes you have to use the = version to ensure the names do not
clash. When importing nested modules, `import B.C` means `import C = B.C`;
the new name is always the last name segment of the module designation.

The ``QualifiedModuleName`` in the ``ModuleImport_`` starts with a
sibling module of the importing module, or with a submodule of the
importing module. There is no way to refer to the parent module, only
sibling modules (and their submodules).

Import statements may occur at the top-level of a program
(that is, in the implicit top-level module of the program) as well.
There they serve simply as a way to give a new name, perhaps a
shorthand name, to a module. For example,

```dafny
module MyModule { ... } // declares module MyModule
import MyModule  // error: cannot add a moduled named MyModule
                 // because there already is one
import M = MyModule // OK. M and MyModule are equivalent
```

## Export Sets

TO BE WRITTEN -- including provides and reveals lists
TO BE WRITTEN -- opened imports are not exported
TO BE WRITTEN -- module facades


## Opening Modules

Sometimes, prefixing the members of the module you imported with the
name is tedious and ugly, even if you select a short name when
importing it. In this case, you can import the module as `opened`,
which causes all of its members to be available without adding the
module name. The `opened` keyword, if present, must immediately follow `import`.
For example, we could write the previous example as:

```dafny
module Mod {
  import opened Helpers
  method m() {
    assert addOne(5) == 6;
  }
}
```

When opening modules, the newly bound members will have low priority,
so they will be hidden by local definitions. This means if you define
a local function called `addOne`, the function from `Helpers` will no
longer be available under that name. When modules are opened, the
original name binding is still present however, so you can always use
the name that was bound to get to anything that is hidden.

```dafny
module Mod {
  import opened Helpers
  function addOne(n: nat): nat {
    n - 1
  }
  method m() {
    assert addOne(5) == 6; // this is now false,
                           // as this is the function just defined
    assert Helpers.addOne(5) == 6; // this is still true
  }
}
```

If you open two modules that both declare members with the same name,
then neither member can be referred to without a module prefix, as it
would be ambiguous which one was meant. Just opening the two modules
is not an error, however, as long as you don't attempt to use members
with common names. The `opened` keyword can be used with any kind of
`import` declaration, including the module abstraction form.

An `import opened` may occur at the top-level as well. For example,
```dafny
module MyModule { ... } // declares MyModule
import opened MyModule // does not declare a new module, but does
                       // make all names in MyModule available in
                       // the current scope, without needing
                       // qualification
import opened M = MyModule // names in MyModule are available in
                       // the current scope without qualification
                       // or qualified with either M or MyModule
```

The Dafny style guidelines suggest using opened imports sparingly.
They are best used when the names being imported have obvious
and unambiguous meanings and when using qualified names would be
verbose enough to impede understanding.

## Module Abstraction

Sometimes, using a specific implementation is unnecessary; instead,
all that is needed is a module that implements some interface.  In
that case, you can use an _abstract_ module import. In Dafny, this is
written `import A : B`.  This means bind the name `A` as before, but
instead of getting the exact module `B`, you get any module which is a
_adheres_ of `B`.  Typically, the module `B` may have abstract type
definitions, classes with bodyless methods, or otherwise be unsuitable
to use directly.  Because of the way refinement is defined, any
refinement of `B` can be used safely. For example, if we start with:

A module that includes an abstract import must be declared _abstract_.

```dafny
module Interface {
  function method addSome(n: nat): nat
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

```dafny
module Implementation {
  function method addSome(n: nat): nat
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}
```

We can then substitute `Implementation` for `A` in a new module, by
declaring a refinement of `Mod` which defines  `A` to be `Implementation`.

```dafny
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

## Module Ordering and Dependencies

Dafny isn't particular about the textual order in which modules are
declared, but
they must follow some rules to be well formed. As a rule of thumb,
there should be a way to order the modules in a program such that each
only refers to things defined **before** it in the ordering. That
doesn't mean the modules have to be given textually in that order in
the source text. Dafny will
figure out that order for you, assuming you haven't made any circular
references. For example, this is pretty clearly meaningless:

```dafny
import A = B
import B = A // error: circular
```

You can have import statements at the toplevel, and you can import
modules defined at the same level:

```dafny
import A = B
method m() {
  A.whatever();
}
module B { ... }
```

In this case, everything is well defined because we can put `B` first,
followed by the `A` import, and then finally `m()`. If there is no
permitted ordering, then Dafny will give an error, complaining about a cyclic
dependency.

Note that when rearranging modules and imports, they have to be kept
in the same containing module, which disallows some pathological
module structures. Also, the imports and submodules are always
considered to be first, even at the toplevel. This means that the
following is not well formed:

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
= B.C`, then this creates a dependency of `A` on `B`, as we need to know
what `B` is (e.g., is it abstract or concrete, or a refinement?).

## Name Resolution

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
an expression context or a type context.

### Expression Context Name Resolution

The leading ``NameSegment`` is resolved using the first following
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
   can always prefix `this` if needed, which cannot be hidden. (Note, a
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

TODO: Not sure about the following paragraph.
Opened modules are treated at each level, after the declarations in the
current module. Opened modules only affect steps 2, 3 and 5. If a
ambiguous name is found, an error is generated, rather than continuing
down the list. After the first identifier, the rules are basically the
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

### Type Context Name Resolution

In a type context the priority of ``NameSegment`` resolution is:

1. Type parameters.

2. Member of enclosing module (type name or the name of a module).

To resolve expression `E.id`:

* If `E` resolved to a module `M`:
  0. Member of module M: a sub-module (including submodules of imports),
     class, datatype, etc.
* If `E` denotes a type:
  1. If `allowDanglingDotName`: Return the type of `E` and the given `E.id`,
     letting the caller try to make sense of the final dot-name.
     TODO: I don't under this sentence. What is `allowDanglingDotName`?
