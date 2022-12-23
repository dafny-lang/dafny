# 3. Programs
````grammar
Dafny = { IncludeDirective_ } { TopDecl } EOF
````
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

A file consists of a sequence of optional _include_ directives followed by top
level declarations followed by the end of the file.

## 3.1. Include Directives
````grammar
IncludeDirective_ = "include" stringToken
````

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

## 3.2. Top Level Declarations
````grammar
TopDecl =
  { DeclModifier }
  ( SubModuleDecl
  | ClassDecl
  | DatatypeDecl
  | NewtypeDecl
  | SynonymTypeDecl  // includes opaque types
  | IteratorDecl
  | TraitDecl
  | ClassMemberDecl(moduleLevelDecl: true)
  )
````
Top-level declarations may appear either at the top level of a Dafny file,
or within a ``SubModuleDecl``. A top-level declaration is one of
various kinds of declarations described later. Top-level declarations are
implicitly members of a default (unnamed) top-level module.

Declarations within a module or at the top-level all begin with reserved keywords and do not end with semicolons.

The ``ClassDecl``, ``DatatypeDecl``, ``NewtypeDecl``,
``SynonymTypeDecl``, ``IteratorDecl``, and ``TraitDecl`` declarations are
type declarations and are described in [Section 6](#sec-types) and
the following sections. Ordinarily
``ClassMemberDecl``s appear in class declarations but they can also
appear at the top level. In that case they are included as part of an
implicit top-level class and are implicitly `static` (but cannot be
declared as static). In addition a ``ClassMemberDecl`` that appears at
the top level cannot be a ``FieldDecl``.

## 3.3. Declaration Modifiers {#sec-declaration-modifiers}
````grammar
DeclModifier = ( "abstract" | "ghost" | "static" )
````

Top level declarations may be preceded by zero or more declaration
modifiers. Not all of these are allowed in all contexts.

The `abstract` modifiers may only be used for module declarations.
An abstract module can leave some entities underspecified.
Abstract modules are not compiled.

The `ghost` modifier is used to mark entities as being used for
specification only, not for compilation to code.

The `static` modifier is used for class members that
are associated with the class as a whole rather than with
an instance of the class.

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
 field                    | ghost
 newtype                  | -
 synonym types            | -
 iterators                | -
 method                   | ghost static
 lemma                    | already-ghost static
 least lemma              | already-ghost static
 greatest lemma           | already-ghost static
 constructor              | -
 function (non-method)    | already-ghost static
 function method          | already-non-ghost static
 predicate (non-method)   | already-ghost static
 predicate method         | already-non-ghost static
 least predicate          | already-ghost static
 greatest predicate       | already-ghost static


