---
title: Is Dafny available as a library, to be called from other software?
---

## Question

Is Dafny available as a library, to be called from other software?

## Answer

Yes, it is. The DafnyPipeline library on NuGet is the most likely candidate for inclusion in a third-party program. The Dafny Playground uses it already (though it doesn’t yet use the NuGet version, since it predates that).

