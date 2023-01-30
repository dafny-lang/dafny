# 3. Programs {#sec-program}
({grammar](#g-program))

At the top level, a Dafny program (stored as files with extension `.dfy`)
is a set of declarations. The declarations introduce (module-level)
constants, methods, functions, lemmas, types (classes, traits, inductive and
coinductive datatypes, newtypes, type synonyms, opaque types, and
iterators) and modules, where the order of introduction is irrelevant. A
class also contains a set of declarations, introducing fields, methods,
and functions.

When asked to compile a program, Dafny looks for the existence of a
Main() method. If a legal Main() method is found, the compiler will emit
an executable appropriate to the target language; otherwise it will emit
a library or individual files.
The conditions for a legal Main() method are described in the User Guide
([Section 25.7.1](#sec-user-guide-main)).
If there is more than one Main(), Dafny will emit an error message.

An invocation of Dafny may specify a number of source files.
Each Dafny file follows the grammar of the ``Dafny`` non-terminal.

A file consists of 
- a sequence of optional _include_ directives, followed by 
- top level declarations, followed by 
- the end of the file.

## 3.1. Include Directives {#sec-include-directive}
([grammar](#g-include-directive))

Examples:
```dafny
include "MyProgram.dfy"
include @"/home/me/MyFile.dfy"
```

Include directives have the form ``"include" stringToken`` where
the string token is either a normal string token or a
verbatim string token. The ``stringToken`` is interpreted as the name of
a file that will be included in the Dafny source. These included
files also obey the ``Dafny`` grammar. Dafny parses and processes the
transitive closure of the original source files and all the included files,
but will not invoke the verifier on the included files unless they have been listed
explicitly on the command line.

The file name may be a path using the customary `/`, `.`, and `..` specifiers.
The interpretation of the name (e.g., case-sensitivity) will depend on the
underlying operating system. A path not beginning with `/` is looked up in
the underlying file system relative to the current working directory (the
one in which the dafny tool is invoked). Paths beginning with a device
designator (e.g., `C:`) are only permitted on Windows systems.

## 3.2. Top Level Declarations {#sec-top-level-declaration}
([grammar](#g-top-level-declaration)

Examples:
```dafny
module M { }
trait R { }
abstract class C { }
dataype D = A | B
newtype pos = i: int | i >= 0
type T = i: int | 0 <= i < 100
static method m() {}
function f(): int
const c: bool
```

Top-level declarations may appear either at the top level of a Dafny file,
or within a (sub)module declaration. A top-level declaration is one of
various kinds of declarations described later. Top-level declarations are
implicitly members of a default (unnamed) top-level module.

Declarations within a module or at the top-level all begin with reserved keywords and do not end with semicolons.

These declarations are one of these kinds:
- methods and functions, encapsulating computations or actions
- const declarations, which are names (of a given type) initialized to an unchanging value
  (declarations of variables are not allowed at the module level)
- type declarations of various kinds ([Section 6](#sec-types) and the following sections)

Methods, functions and const declarations are placed in an implicit class declaration
that is in the top-level implicit module. These declarations are all implicitly
`static` (but may not be declared explicitly static).

## 3.3. Declaration Modifiers {#sec-declaration-modifier}
([grammar](#g-declaration-modifier))

Examples:
,!-- %check-resolve -->
```dafny
abstract module M {}
static method m() {}
ghost function f(): int { 0 }
```

Top level declarations may be preceded by zero or more declaration
modifiers. Not all of these are allowed in all contexts.

The `abstract` modifier may only be used for module declarations.
An abstract module can leave some entities underspecified.
Abstract modules are not compiled.

The `ghost` modifier is used to mark entities as being used for
specification only, not for compilation to code.

The `static` modifier is used for class members that
are associated with the class as a whole rather than with
an instance of the class. This modifier may not be used with
declarations that are implicitly static, as are members of the 
top-level, unnamed implicit class.

<!-- TBD - opaque ? Add example above when it is implemented --> 

The following table shows modifiers that are available
for each of the kinds of declaration. In the table
we use already-ghost (already-non-ghost) to denote that the item is not
allowed to have the ghost modifier because it is already
implicitly ghost (non-ghost).


 Declaration              | allowed modifiers
--------------------------|---------------------------------------
 module                   | abstract
 class                    | -
 trait                    | -
 datatype or codatatype   | -
 field (const)            | ghost
 newtype                  | -
 synonym types            | -
 iterators                | -
 method                   | ghost static
 lemma                    | already-ghost static
 least lemma              | already-ghost static
 greatest lemma           | already-ghost static
 constructor              | ghost
 function                 | ghost static             (Dafny 4)
 function method          | already-non-ghost static (Dafny 3)
 function (non-method)    | already-ghost static     (Dafny 3)
 predicate                | ghost static             (Dafny 4)
 predicate method         | already-non-ghost static (Dafny 3)
 predicate (non-method)   | already-ghost static     (Dafny 3)
 least predicate          | already-ghost static
 greatest predicate       | already-ghost static


