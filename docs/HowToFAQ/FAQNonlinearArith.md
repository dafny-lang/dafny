---
title: How can I improve automation and performance for programs with non-linear arithmetic?
---

## Question

How can I improve automation and performance for programs with non-linear arithmetic?

## Answer

There are some switches (/arith and the somewhat deprecated /noNLarith) that reduce the automation you get with nonlinear arithmetic; they improve the overall proof success by using manually introduced lemmas instead. There are now also many lemmas about nonlinear arithmetic in the Dafny standard library.
