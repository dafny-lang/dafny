# 3. Programs ([grammar](#g-program)) {#sec-program}

At the top level, a Dafny program (stored as files with extension `.dfy`)
is a set of declarations. The declarations introduce (module-level)
constants, methods, functions, lemmas, types (classes, traits, inductive and
coinductive datatypes, newtypes, type synonyms, opaque types, and
iterators) and modules, where the order of introduction is irrelevant. 
Some types, notably classes, also may contain a set of declarations, introducing fields, methods,
and functions.

When asked to compile a program, Dafny looks for the existence of a
`Main()` method. If a legal `Main()` method is found, the compiler will emit
an executable appropriate to the target language; otherwise it will emit
a library or individual files.
The conditions for a legal `Main()` method are described in the User Guide
([Section 3.4](#sec-user-guide-main)).
If there is more than one `Main()`, Dafny will emit an error message.

An invocation of Dafny may specify a number of source files.
Each Dafny file follows the grammar of the ``Dafny`` non-terminal.

A file consists of 
- a sequence of optional _include_ directives, followed by 
- top level declarations, followed by 
- the end of the file.

## 3.1. Include Directives ([grammar](#g-include-directive)) {#sec-include-directive}

Examples:
<!-- %no-check -->
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
explicitly on the command line or the `--verify-included-files` option is
specified.

The file name may be a path using the customary `/`, `.`, and `..` punctuation.
The interpretation of the name (e.g., case-sensitivity) will depend on the
underlying operating system. A path not beginning with `/` is looked up in
the underlying file system relative to the 
_location of the file in which the include directive is stated_. 
Paths beginning with a device
designator (e.g., `C:`) are only permitted on Windows systems.
Better style advocates using relative paths in include directives so that
groups of files may be moved as a whole to a new location.

Paths of files on the command-line or named in `--library` options are 
relative the the current working directory.

## 3.2. Top Level Declarations ([grammar](#g-top-level-declaration)) {#sec-top-level-declaration}

Examples:
<!-- %check-resolve -->
```dafny
abstract module M { }
trait R { }
class C { }
datatype D = A | B
newtype pos = i: int | i >= 0
type T = i: int | 0 <= i < 100
method m() {}
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
- const declarations, which are names (of a given type) initialized to an unchanging value;
  declarations of variables and mutable fields are not allowed at the module level
- type declarations of various kinds ([Section 5](#sec-types) and the following sections)

Methods, functions and const declarations are placed in an implicit class declaration
that is in the top-level implicit module. These declarations are all implicitly
`static` (and may not be declared explicitly static).

## 3.3. Declaration Modifiers ([grammar](#g-declaration-modifier)) {#sec-declaration-modifier}

Examples:
<!-- %check-resolve -->
```dafny
abstract module M {
  class C {
    static method m() {}
  }
}
ghost opaque const c : int
```

Top level declarations may be preceded by zero or more declaration
modifiers. Not all of these are allowed in all contexts.

The `abstract` modifier may only be used for module declarations.
An abstract module can leave some entities underspecified.
Abstract modules are not compiled.

The `ghost` modifier is used to mark entities as being used for
specification only, not for compilation to code.

The `opaque` modifier may be used on const declarations and functions.

The `static` modifier is used for class members that
are associated with the class as a whole rather than with
an instance of the class. This modifier may not be used with
declarations that are implicitly static, as are members of the 
top-level, unnamed implicit class.

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
 field (const)            | ghost opaque
 newtype                  | -
 synonym types            | -
 iterators                | -
 method                   | ghost static
 lemma                    | already-ghost static
 least lemma              | already-ghost static
 greatest lemma           | already-ghost static
 constructor              | ghost
 function                 | ghost static opaque             (Dafny 4)
 function method          | already-non-ghost static opaque (Dafny 3)
 function (non-method)    | already-ghost static opaque     (Dafny 3)
 predicate                | ghost static opaque             (Dafny 4)
 predicate method         | already-non-ghost static opaque (Dafny 3)
 predicate (non-method)   | already-ghost static opaque     (Dafny 3)
 least predicate          | already-ghost static opaque
 greatest predicate       | already-ghost static opaque


## 3.4. Executable programs {#sec-user-guide-main}

Dafny programs have an important emphasis on verification, but the programs 
may also be executable.

To be executable, the program must have exactly one `Main` method and that 
method must be a legal main entry point.

* The program is searched for a method with the attribute `{:main}`.
If exactly one is found, that method is used as the entry point; if more
than one method has the `{:main}` attribute, an error message is issued.
* Otherwise, the program is searched for a method with the name `Main`.
If more than one is found an error message is issued.

Any abstract modules are not searched for candidate entry points,
but otherwise the entry point may be in any module or type. In addition,
an entry-point candidate must satisfy the following conditions:

* The method has no type parameters and either has no parameters or one non-ghost parameter of type `seq<string>`.
* The method has no non-ghost out-parameters.
* The method is not a ghost method.
* The method has no requires or modifies clauses, unless it is marked `{:main}`.
* If the method is an instance (that is, non-static) method and the
  enclosing type is a class,
  then that class must not declare any constructor.
  In this case, the runtime system will
  allocate an object of the enclosing class and will invoke
  the entry-point method on it.
* If the method is an instance (that is, non-static) method and the
  enclosing type is not a class,
  then the enclosing type must, when instantiated with auto-initializing
  type parameters, be an auto-initializing type.
  In this case, the runtime system will
  invoke the entry-point method on a value of the enclosing type.

Note, however, that the following are allowed:

* The method is allowed to have `ensures` clauses
* The method is allowed to have `decreases` clauses, including a
  `decreases *`. (If `Main()` has a `decreases *`, then its execution may
  go on forever, but in the absence of a `decreases *` on Main(), `dafny`
  will have verified that the entire execution will eventually
  terminate.)

If no legal candidate entry point is identified, `dafny` will still produce executable output files, but
they will need to be linked with some other code in the target language that
provides a `main` entry point.

If the `Main` method takes an argument (of type `seq<string>`), the value of that input argument is the sequence
of command-line arguments, with the first entry of the sequence (at index 0) being a system-determined name for the 
executable being run.

The exit code of the program, when executed, is not yet specified.
