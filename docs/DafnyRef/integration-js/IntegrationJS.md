---
title: Integrating Dafny and JavaScript code
---

The Dafny compilation process for Javascript translates Dafny programs into target language
source code (`.js` files), and then potentially runs the result. 

The Dafny-to-Javascript compiler writes out the translated files of a file _A_`.dfy`
to a single _A_`.js` file. 

A multi-language program that combines Dafny and Javascript
code "just" needs to be sure that the translated Dafny code fits in
to the Javascript code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Javascript
- ensuring that the types are the same on both sides, which can be tricky as JavaScript is dynamically typed

## **The Dafny runtime library**

The step of running Javascript files (using `node`) requires the Dafny runtime library. 
That library is automatically included in the resulting `.js` file if `dafny` is doing the compilation,
but not if `dafny` is only doing translation.

## **Manually executing Dafny-generated Javascript code**

Suppose a Dafny program is contained in a .dfy files, A.dfy, which contains the Dafny `Main` method. One can build the corresponding Javascript program (without running it) using this command:

`dafny build --target:js A.dfy`

The program is then executed using the command
`node A.js`

The combined build-and-run command is `dafny run --target:js A.dfy`.

## Combining Dafny and Javascript source files

The dafny tool  is not yet able to automatically combine Dafny and Javascript source files.

## Equality of extern types

A Dafny `class` or `trait` has object identity, and the verifier assumes that
`==` and the built-in collections compare such values by identity. An extern
JavaScript object is compared by identity unless it defines an `equals` method,
which is how an extern value type opts in to structural equality; overriding it
to give a structural equality lets a compiled program contradict what the
verifier proved. A type whose equality should be structural is better modelled
as a Dafny `datatype`, or, when it must be backed by JavaScript code, as an
opaque value type `type {:extern} T(==)`, whose equality the verifier leaves
uninterpreted and whose JavaScript `equals` is then used at run time without
contradicting any verified fact.
