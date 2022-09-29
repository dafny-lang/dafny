A Dafny adaptation of some of [Xavier Leroy's compiler verification tutorial](https://xavierleroy.org/courses/EUTypes-2019/).

To verify the whole proof:
```
dafny /compile:0 CompileProgramCorrect.dfy
```

## Abstract Semantics

* [Common.dfy](Common.dfy): identifier and store
* [Semantics.dfy](Semantics.dfy): inductive and coinductive closures of reductions

## Languages: syntax and semantics

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

