---
title: When I try to compile and run the .jave file produced by Dafny, I get errors about missing packages. Where are they?
---

## Question

When I try to compile and run the .jave file produced by Dafny, I get errors about missing packages. Where are they?

## Answer

Typically, when Dafny compiles a `X.dfy` file to java, it places the output source files in a folder named `X-java` by default.
It writes the main program to `X.java`, but writes other source files and a runtime .jar file as well.

To compile the Java source, run `javac -cp X-java:X-java/DafnyRuntime.jar X-java/X.java`
and then to run the copmpiled program, `java  -cp X-java:X-java/DafnyRuntime.jar X`
