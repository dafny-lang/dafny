# Programs
````grammar
Dafny = { IncludeDirective_ } { TopDecl } EOF
````
At the top level, a Dafny program (stored as files with extension `.dfy`)
is a set of declarations. The declarations introduce (module-level)
constants, methods, functions, lemmas, types (classes, traits, inductive and
co-inductive datatypes, new_types, type synonyms, opaque types, and
iterators) and modules, where the order of introduction is irrelevant. A
class also contains a set of declarations, introducing fields, methods,
and functions.

When asked to compile a program, Dafny looks for the existence of a
Main() method. If a legal Main() method is found, the compiler will emit
a `.EXE`; otherwise, it will emit a `.DLL`.

 (If there is more than one Main(), Dafny will try to emit an .EXE, but
 this may cause the C\# compiler to complain. One could imagine improving
 this functionality so that Dafny will produce a polite error message in
 this case.)

In order to be a legal Main() method, the following must be true:

* The method takes no parameters
* The method is not a ghost method
* The method has no requires clause
* The method has no modifies clause
* If the method is an instance (that is, non-static) method in a class,
  then the enclosing class must not declare any constructor

Note, however, that the following are allowed:

* The method is allowed to be an instance method as long as the enclosing
  class does not declare any constructor. In this case, the runtime
  system will allocate an object of the enclosing class and will invoke
  Main() on it.
* The method is allowed to have `ensures` clauses
* The method is allowed to have `decreases` clauses, including a
  `decreases *`. (If Main() has a `decreases *`, then its execution may
  go on forever, but in the absence of a `decreases *` on Main(), Dafny
  will have verified that the entire execution will eventually
  terminate.)

An invocation of Dafny may specify a number of source files.
Each Dafny file follows the grammar of the ``Dafny`` non-terminal.

It consists of a sequence of optional _include_ directives followed by top
level declarations followed by the end of the file.

## Include Directives
````grammar
IncludeDirective_ = "include" stringToken
````

Include directives have the form ``"include" stringToken`` where
the string token is either a normal string token or a
verbatim string token. The ``stringToken`` is interpreted as the name of
a file that will be included in the Dafny source. These included
files also obey the ``Dafny`` grammar. Dafny parses and processes the
transitive closure of the original source files and all the included files,
but will not invoke the verifier on these unless they have been listed
explicitly on the command line.

The file name may be a path using the customary `/`, `.`, and `..` specifiers.
The interpretation of the name (e.g., case-sensitivity) will depend on the
underlying operating system. A path not beginning with `/` is looked up in 
the underlying file system relative to the current working directory (the
one in which the dafny tool is invoked). Paths beginning with a device
designator (e.g., `C:`) are only permitted on Windows systems.

## Top Level Declarations
````grammar
TopDecl = { { DeclModifier }
  ( SubModuleDecl
  | ClassDecl
  | DatatypeDecl
  | NewtypeDecl
  | SynonymTypeDecl
  | IteratorDecl
  | TraitDecl
  | ClassMemberDecl(moduleLevelDecl: true)
  }
````
Top-level declarations may appear either at the top level of a Dafny file,
or within a ``SubModuleDecl``. A top-level declaration is one of the 
various kinds of declarations described later. Top-level declarations are
implicitly members of a default (unnamed) top-level module.

The ``ClassDecl``, ``DatatypeDecl``, ``NewtypeDecl``,
``SynonymTypeDecl``, ``IteratorDecl``, and ``TraitDecl`` declarations are
type declarations and are describe in Section [#sec-types]. Ordinarily
``ClassMemberDecl``s appear in class declarations but they can also
appear at the top level. In that case they are included as part of an
implicit top-level class and are implicitly `static` (but cannot be
declared as static). In addition a ``ClassMemberDecl`` that appears at
the top level cannot be a ``FieldDecl``.

## Declaration Modifiers
````grammar
DeclModifier =
  ( "abstract" | "ghost" | "static" | "protected"
  | "extern" [ stringToken]
  )
````

Top level declarations may be preceded by zero or more declaration
modifiers. Not all of these are allowed in all contexts.

The `abstract` modifiers may only be used for module declarations.
An abstract module can leave some entities underspecified.
Abstract modules are not compiled to C\#.

The `ghost` modifier is used to mark entities as being used for
specification only, not for compilation to code.

The `static` modifier is used for class members that that
are associated with the class as a whole rather than with
an instance of the class.

The `protected` modifier is used to control the visibility of the
body of functions.

The `extern` modifier is used to alter the CompileName of
entities. The CompileName is the name for the entity
when translating to Boogie or a target programming language.

The following table shows modifiers that are available
for each of the kinds of declaration. In the table
we use already-ghost (already-non-ghost) to denote that the item is not
allowed to have the ghost modifier because it is already
implicitly ghost (non-ghost).


 Declaration              | allowed modifiers                     
--------------------------|---------------------------------------
 module                   | abstract                              
 class                    | extern                                
 trait                    | -                                     
 datatype or codatatype   | -                                     
 field                    | ghost                                 
 newtype                  | -                                     
 synonym types            | -                                     
 iterators                | -                                     
 method                   | ghost static extern                   
 lemma, colemma, comethod | already-ghost static protected        
 inductive lemma          | already-ghost static                  
 constructor              | -                                     
 function (non-method)    | already-ghost static protected        
 function method          | already-non-ghost static protected extern 
 predicate (non-method)   | already-ghost static protected        
 predicate method         | already-non-ghost static protected extern 
 inductive predicate      | already-ghost static protected        
 copredicate              | already-ghost static protected        



