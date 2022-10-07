---
title: Why do I need to use an old version of Z3?
---

## Question

Why do I need to keep using an old version of Z3?

## Answer

It is correct that the version of Z3 used by Dafny (through Boogie) is an old version.
Although the Dafny team would like to upgrade to newer versions of Z3 (to take advantage
of bug fixes, at a minimum), so far the newer versions of Z3 perform more poorly on
Dafny-generated SMT for many test cases.
