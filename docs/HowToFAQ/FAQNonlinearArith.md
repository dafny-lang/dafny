---
title: Are there any useful tricks (e.g. z3 switches) to get better automation for nonlinear arithmetic (perhaps trading off other performance aspects)?
---

## Question

Are there any useful tricks (e.g. z3 switches) to get better automation for nonlinear arithmetic (perhaps trading off other performance aspects)?

## Answer

No. There are some switches (/arith and the somewhat deprecated /noNLarith) that reduce the automation you get with nonlinear arithmetic. There are now also many lemmas about nonlinear arithmetic in the Dafny standard library.
