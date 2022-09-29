A Dafny adaptation of some of [Xavier Leroy's compiler verification tutorial](https://xavierleroy.org/courses/EUTypes-2019/).

To verify the whole proof:
```
dafny /compile:0 CompileProgramCorrect.dfy
```

# High-Level Project Description

## Abstract Semantics

* [Semantics.dfy](Semantics.dfy): inductive and coinductive closures of reductions
* [SemanticsProperties.dfy](SemanticsProperties.dfy)

## Languages: syntax and semantics

* [SyntaxCommon.dfy](SyntaxCommon.dfy): both languages share the concept of an identifier
* [SemanticsCommon.dfy](SemanticsCommon.dfy): all semantics use the concept of a store associating identifiers to integer values

| Language | Imp    | Mach   |
| -------- | ------ | ------ |
| Syntax | [Imp.dfy](Imp.dfy) | [Mach.dfy](Mach.dfy) |
| Natural semantics | [ImpNaturalSem.dfy](ImpNaturalSem.dfy) | |
| Reduction semantics | | [MachSemantics.dfy](MachSemantics.dfy) | 

## Compiler

* [Compiler.dfy](Compiler.dfy)

## Proof of semantics preservation

* [SimulationRelation.dfy](SimulationRelation.dfy): matching of program states
* [CompileAexpCorrect.dfy](CompileAexpCorrect.dfy): correctness of compilation of arithmetic expressions
* [CompileBexpCorrect.dfy](CompileBexpCorrect.dfy): correctness of compilation of Boolean expressions
* [CompileComCorrect.dfy](CompileComCorrect.dfy): correctness of compilation of commands
* [CompileProgramCorrect.dfy](CompileProgramCorrect.dfy): correctness of compilation of whole program

# Linear Project Description

## Dafny: a functional programming language

The Dafny programming language contains a functional core with datatypes, pattern-matching, functions as values, and parametric polymorphism.
It has Call-by-value semantics and Rank-1 polymorphism, but not with HM inference

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SyntaxCommon.dfy](SyntaxCommon.dfy) | types | |
| [Imp.dfy](Imp.dfy) | datatypes | |
| [Mach.dfy](Mach.dfy) | sequences, type operators, polymorphism | |
| [Compiler.dfy](Compiler.dfy) | functions, pattern-matching, conditional expressions, let-binding | |

## Dafny: a specification language

Dafny's logic contains Church's simple type theory with rank-1 polymorphism and datatypes. It is impredicative. Therefore, it includes Leibniz equality, propositional and first-order logic.

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SemanticsCommon.dfy](SemanticsCommon.dfy) | maps | |
| [ImpNaturalSem.dfy](ImpNaturalSem.dfy) | predicates, least predicates, first-order logic | |
| [Semantics.dfy](Semantics.dfy) | greatest predicate | |
| [MachSemantics.dfy](MachSemantics.dfy) | | |

## Dafny: a proof system

Dafny's proofs are written using a small set of statements that are higher-level than tactics.
For example, you can simulate the rules of [Hilbert's systems](Hilbert.dfy), [natural deduction](NaturalDeduction.dfy), and [sequent calculus](SequentCalculus.dfy).

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SimulationRelation.dfy](SimulationRelation.dfy) | lemmas, proofs | |
| [SemanticsProperties.dfy](SemanticsProperties.dfy) | transfinite induction | |
| [CompileAexpCorrect.dfy](CompileAexpCorrect.dfy) | induction | |
| [CompileBexpCorrect.dfy](CompileBexpCorrect.dfy) | | |
| [CompileComCorrect.dfy](CompileComCorrect.dfy) |  | |
| [CompileProgramCorrect.dfy](CompileProgramCorrect.dfy) | | |

  
