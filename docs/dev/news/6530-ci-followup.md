# PR #6530 — CI follow-up (status)

Two integration-test shards went red on the C++ backend. Two independent causes,
both fixed here.

## Cause 1: a stray runtime file changed the C++ output
`comp/compile1verbose/CompileAndThenRun`, `comp/compile3/JustRun`,
`comp/manualcompile/ManualCompile` all diffed on one extra line:
`Additional output written to runtime_print_smoketest.cpp`.

The C++ backend copies out every embedded `DafnyRuntimeCpp/**/*.cpp` at compile
time. The added `runtime_print_smoketest.cpp` got swept in and printed that line,
which the three `.expect` files don't have.

**Fix:** deleted `runtime_print_smoketest.cpp`. It was a hand-run standalone check
(no build/test target compiled it), and the real `c++/*.dfy` lit tests already
cover the same printing. The three `.expect` files were left untouched.

## Cause 2: datatype printing missed the array field type
`c++/arrays.dfy` (and `git-issue-1100`, which includes it) stopped compiling with
`no match for operator<< ... DafnyArray<unsigned int>`.

This PR makes the C++ backend emit `operator<<` for every datatype. `arrays.dfy`
has `datatype ArrayDatatype = AD(ar: array<uint32>)`, so the generated operator
instantiates `dafny_print_to` on an array field, and `DafnyRuntime.h` had no
`operator<<` for `DafnyArray<T>`. On master this never surfaced because datatypes
had no `operator<<` at all (printing a datatype value simply didn't compile).

**Fix:** added `operator<<` for `DafnyArray<T>` in `DafnyRuntime.h`, printing
`array[<len>]`. Nothing actually prints a bare array; the other backends print an
opaque identity there. The operator only needs to exist so the emitted datatype
operator compiles.

## Note on scope
Datatype value printing is new behavior, not a fix: on master `print` of a
datatype didn't compile at all. The rest (collection format, map last-wins,
8-bit newtypes, codatatype reject) are fixes.

## Verification
Local: solution builds clean; `Executing on C++...` now compiles with no error in
all four tests, and the `runtime_print_smoketest` line is gone from the three
comp tests. Full multi-backend `.expect` diffs weren't reproduced locally, since
the local harness trips over the internal Rust generator and output-dir setup.
CI is the gate for the final green.
