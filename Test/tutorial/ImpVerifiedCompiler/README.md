Warning: work in progress. Dafny's explanations are currently incomplete and could sometimes be misleading.

A Dafny adaptation of some of [Xavier Leroy's compiler verification tutorial](https://xavierleroy.org/courses/EUTypes-2019/).

To verify the whole proof:
```
dafny /compile:0 CompileProgramCorrect.dfy
```

If you are familiar with Dafny, you should consider reading the high-level project description. Note that we are exploring proof readability, so some proofs might be a lot more verbose than you might like.

If you are not familiar with Dafny, you should consider reading the linear project description. If you are already familiar with functional programming, proof assistants, and basic compilers, you will be introduced to just enough Dafny (with a slingshot) to allow you to learn Dafny by reading the compiler verification from line 1 till the end

> Lewis Carroll - Alice's Adventures in Wonderland - “Begin at the beginning," the King said, very gravely,"and go on till you come to the end: then stop.”

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

The following presentation is intended for people who are not familiar with Dafny but are familiar with functional programming, proof assistants, and basic compilers. 
You can read the files in order and we introduce Dafny's prerequisites along the way. 

Hopefully, by the time your are done reading, you will be able to develop verified code in Dafny as well as you might have using another proof assistant. However, note that we only present a subset of Dafny which is enough to be productive, but not representative of its richness.

## Dafny: a functional programming language

### Prelude

Dafny is a programming language. It contains a functional core with the following features:

* Functions as first class citizens, always de-currified, with call-by-value semantics
* Statically typed, with type inference
* Rank-1 polymorphism, no Hindly-Milner inference
* Datatypes and pattern matching
* Modules (In the following, modules are used only for namespace management)

The following example demonstrates the subset of Dafny we use in the compiler verification.

* The body of a function is an expression and the variable introduction is a let-binding
* const are declare top-level constants
* predicate is just syntactic sugar for a Boolean-valued function

```dafny
module GenList {

  datatype List<T> =
    | Nil
    | Cons(T, List<T>)

  function method filter<T>(p: T -> bool, l: List<T>): List<T> {
    match l {
      case Nil => Nil
      case Cons(head,tail) =>
        var rest := filter(p,tail);
        if p(head) then Cons(head,rest) else rest 
    }
  }
	
}

module IntList {

  import opened GenList

  const example: List<int> := Cons(-3,Cons(4,Nil))

  predicate method is_non_negative(n: int) {
    n >= 0
  }

  const filtered_example: List<int> := filter(is_non_negative,example) 
		
}
```

### Onward!

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SyntaxCommon.dfy](SyntaxCommon.dfy) | types | |
| [Imp.dfy](Imp.dfy) | datatypes | |
| [Mach.dfy](Mach.dfy) | sequences, type operators, polymorphism | |
| [Compiler.dfy](Compiler.dfy) | functions, pattern-matching, conditional expressions, let-binding | |

## Dafny: a logic

### Prelude

Dafny's logic contains a core that is reminiscent of Church's simple type theory and LCF.  It is [impredicative](TutorialSupport/Impredicative.dfy). 

The following example demonstrates the specification of some theory of arithmetic:

* We can posit the existence of constants, functions, predicates (using datatypes or by ommitting definitions)
* We can declare axiom (lemmas)
* We can use connectives of propositional logic and quantifiers of predicate logic

```dafny
datatype Nat =
  | Z
  | S(Nat)

function plus(x: Nat, y: Nat): Nat

function times(x: Nat, y: Nat): Nat

lemma peano1()
  ensures forall x, y: Nat :: S(x) == S(y) ==> x == y

lemma peano2()
  ensures forall x: Nat :: ! (Z == S(x))

lemma peano3()
  ensures forall P: Nat -> bool :: P(Z) && (forall x: Nat :: P(x) ==> P(S(x))) ==> forall y: Nat :: P(y)

lemma peano4()
  ensures forall x: Nat :: plus(Z,x) == x
	
predicate even(n: Nat) {
  exists m: Nat :: n == times(m,S(S(Z)))
}
```

### Onward!

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SemanticsCommon.dfy](SemanticsCommon.dfy) | maps | |
| [ImpNaturalSem.dfy](ImpNaturalSem.dfy) | predicates, least predicates, first-order logic | |
| [Semantics.dfy](Semantics.dfy) | greatest predicate | |
| [MachSemantics.dfy](MachSemantics.dfy) | | |

## Dafny: a proof assistant

### Prelude

Dafny is a proof assistant. You can interactively prove a lemma, and you do so by giving the lemma a body. 
As a first approximation, you can think of a lemma as a sequent and its body as a proof script. 

Consider following example:
```dafny	
lemma two_plus_two_equals_four(a: nat, b: nat)
  requires exists a': nat :: a == 2 * a'
  requires exists b': nat :: b == 2 * b'
  ensures exists k: nat :: a + b == 2 * k
{
  var a' :| a == 2 * a';
  var b' :| b == 2 * b';
  assert a + b == 2 * a' + 2 * b';
  assert a + b == 2 * (a' + b');
}
```

This lemma can be interpreted as the sequent: $a: nat,  b: nat,  \exists a': nat, a = 2 * a',  \exists b': nat, b = 2 * b' \vdash \exists k: nat, a + b = 2 \times k$ where
* Every parameter (type or value) is in the antecedants
* Every require is in the antecedants
* Every ensure is in the consequents

Note, however, that a lemma with n ensures, where n is greater than 1, should not be interpreted as 1 but n sequents. 

The body of the lemma can be interpreted as a proof script. The semantics of the proof script is given by weakest-preconditions, but you do not have to think about the proof script as such. Indeed, you can simulate the rules of [Hilbert's systems](TutorialSupport/Hilbert.dfy), [natural deduction](TutorialSupport/NaturalDeduction.dfy), and [sequent calculus](TutorialSupport/SequentCalculus.dfy). 

Perhaps the simplest way to interpret (and write) proof scripts for proofs that are not tightly connected to code is to think by natural deduction.

A few final comments:
* [Dafny is classical](TutorialSupport/Classic.dfy)
* [Dafny is not linear](TutorialSupport/NotLinear.dfy)
* [Dafny has choice](TutorialSupport/Choice.dfy)
* [Proofs are not first-class](TutorialSupport/ProofIrrelevance.dfy)

### Onward!

| File   | New concepts | Notes    |
| ------ | ------------ | -------- |
| [SimulationRelation.dfy](SimulationRelation.dfy) | lemmas, proofs | |
| [SemanticsProperties.dfy](SemanticsProperties.dfy) | transfinite induction | |
| [CompileAexpCorrect.dfy](CompileAexpCorrect.dfy) | induction | |
| [CompileBexpCorrect.dfy](CompileBexpCorrect.dfy) | | |
| [CompileComCorrect.dfy](CompileComCorrect.dfy) |  | |
| [CompileProgramCorrect.dfy](CompileProgramCorrect.dfy) | | |

  
