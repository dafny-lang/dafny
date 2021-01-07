# 23. Refinement {#sec-module-refinement}

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
```
module P { // refinement parent
}
module M refines P { // refining module
}
```

The refinement result is created as follows.

0) The refinement result is a module within the same enclosing module as the
refining module, has the same name, and in fact replaces the refining module  in their shared scope.

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
directives and mayt refer to names copied from the refinement parent,
resolution of names and types of the declarations copied in this step is
performed in the context of the full refinement result.

3) Where declarations in the parent and refinement module have the same name,
the second refines the first and the combination, a refined declaration, is
the result placed in the refinement result module, to the exclusion of the
declarations with the same name from the parent and refinement modules.

The way the refinement result declarations are assembled depends on the kind of declaration;
the rules are described in subsections below.

So that it is clear that refinment is taking place, refining declarations
have some syntactic indicator that they are refining some parent declaration.
Typically this is the presence of a `...` token.

## 23.1. Export set declarations

A refining export set declaration begins with the syntax
```grammar
"export" Ident "..." 
```
but otherwise contains the same `provides`, `reveals` and `extends` sections,
with the ellipsis indicating that it is a refining declaration.

The result declaration has the same name as the two input declarations and the unions of names from each of the `provides`, `reveals`, and `extends`
sections, respectively.

An unnamed export set declaration from the parent is copied into the result
module with the name of the parent module. The result module has a default
export set according to the general rules for export sets, after all of 
the result module's export set declarations have been assembled.

## 23.2. Import declarations

Aliasing import declarations are not refined. The result module contains the union
of the import declarations from the two input modules.
There must be no names in common among them.

Abstract import declarations (declared with `:` instead of `=`, [Section 0](#sec-module-abstraction)) are refined. The refinement parent contains the 
abstract import and the refining module contains a regular aliasing
import for the same name. Dafny checks that the refining import _adheres_ to
the abstract import.

## 23.3. Sub-module declarations

TODO

## 23.4. Const declarations

A parent `const` declaration may be refined by a refining `const` declaration
if

* the parent has no initialization, 
* the child has the same type as the parent, and
* one or both of the following holds:
   * the child has an initializing expression
   * the child is declared `ghost` and the parent is not `ghost`, or vice versa

To indicate it is a refining declaration, a refining `const` declaration
contains an ellipsis in this syntax:
```grammar
"const" { Attribute } CIdentType "..." [ ":=" Expression ]
```

## 23.5. Method declarations

TODO

## 23.6. Lemma declarations

TODO

## 23.7. Function and predicate declarations

TODO

## 23.8. Iterator declarations

TODO

## 23.9. Class and trait declarations

TODO

## 23.10. Type declarations
-- opaque, type synonym, subset, newtype, datatype

TODO

