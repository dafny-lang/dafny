A Dafny adaptation of some of [Xavier Leroy's compiler verification tutorial](https://xavierleroy.org/courses/EUTypes-2019/).

To verify the whole proof:
```
dafny /compile:0 CompileProgramCorrect.dfy
```

# High-Level Project Description

## Abstract Semantics

* [Semantics.dfy](Semantics.dfy): inductive and coinductive closures of reductions

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

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SyntaxCommon.dfy](SyntaxCommon.dfy) | | |
| [Imp.dfy](Imp.dfy) | | |
| [Mach.dfy](Mach.dfy) | | |
| [Compiler.dfy](Compiler.dfy) | | |

## Dafny: a specification language

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SemanticsCommon.dfy](SemanticsCommon.dfy) | | |
| [ImpNaturalSem.dfy](ImpNaturalSem.dfy) | | |
| [Semantics.dfy](Semantics.dfy) | | |
| [MachSemantics.dfy](MachSemantics.dfy) | | |

## Dafny: a proof system

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SimulationRelation.dfy](SimulationRelation.dfy) | | |
| [CompileAexpCorrect.dfy](CompileAexpCorrect.dfy) | | |
| [CompileBexpCorrect.dfy](CompileBexpCorrect.dfy) | | |
| [CompileComCorrect.dfy](CompileComCorrect.dfy) | | |
| [CompileProgramCorrect.dfy](CompileProgramCorrect.dfy) | | |

  
