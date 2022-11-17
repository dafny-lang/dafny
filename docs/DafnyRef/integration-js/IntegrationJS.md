---
title: Integrating Dafny and JavaScript code
---

The Dafny compilation process for Javascript translates Dafny programs into target language
source code (`.js` files), and then potentially runs the result. 

The Dafny-to-Javascript compiler writes out the translated files of a file _A_`.dfy`
to a single _A_`.js` file. 

A multi-language program that combines Dafny and Javascript
code "just" needs to be sure that the translated Dafny code fits in
to the Java code. There are two aspects to this:
- ensuring that the names of entities in the translated Dafny code are usable from Java
- ensuring that the types are the same on both sides, which can be tricky as Javascriupt is dynamically typed

## **The Dafny runtime library**

The step of running Javascript files (using `node`) requires the Dafny runtime library. 
That library is automatically included in the resulting `.js` file if `dafny` is doing the compilation,
but not if `dafny` is only doing translation..

## **Manually executing Dafny-generation Java code**

Suppose a Dafny program is contained in a .dfy files, A.dfy, which contains the Dafny `Main` method. One can build the corresponding Javascript program (without running it) using this command:

`dafny build --target:js A.dfy`

The program is then executed using the command
`node A.js`

The combined build-and-run command is `dafny run --target:js A.dfy`.

## Combining Dafny and Javascript source files

The dafny tool  is not yet able to automatically combine Dafny and Javascript source files.
