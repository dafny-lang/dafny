---
title: "Prover error: Unexpected prover response (getting info about 'unknown' response): (:reason-unknown 'Overflow encountered when expanding old_vector')"
---

This error is caused by a bug in the Z3 backend tool used by Dafny. 
As of v3.9.0 there is work underway to update Z3 to a more recent version.
Until then, the best you can do is to try to change the verification condition sent to Z3 by splitting it up, using various Dafny options and attributes like `{:split_here}`, `{:focus}`, `/vcsSplitOnEveryAssert`, `/vcsMaxSplits`, and `/randomSeed`.

