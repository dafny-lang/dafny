# DafnyRuntimeGo-gomod

This directory holds the DafnyRuntimeGo library code compatible with Go modules. We need this apart from the regular
`DafnyRuntimeGo` because the compiler supports generating code in both formats - GoPath and GoModule. In long term, this
should be published as an independent Go module: https://github.com/dafny-lang/dafny/issues/494 .

This has been checked in to provide the library for testing and can serve as source-of-truth for publishing the final
GoModule. And once compiler has deprecated the support for GoPath, we should remove the existing `DafnyRuntimeGo` and
drop the `-gomod` from this directory to make it the sole runtime for Go.