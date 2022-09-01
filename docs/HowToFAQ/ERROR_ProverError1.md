---
title: "Prover error: Unexpected prover response (getting info about 'unknown' response): (:reason-unknown 'Overflow encountered when expanding old_vector')"
---

This error is caused by a Z3 bug. The best you can do is to try to change the verification condition sent to Z3 by splitting it up, using various options and attributes like `{:split_here}`, `{:focus}`, `/vcsSplitOnEveryAssert`, `/vcsMaxSplits`, and `/randomSeed`.
