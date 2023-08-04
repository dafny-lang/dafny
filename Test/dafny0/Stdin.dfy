// RUN: %exits-with 0 %stdin "module A{}" %baredafny verify --show-snippets:false --stdin > "%t"
// RUN: %exits-with 4 %stdin "method a() { assert false; }" %baredafny verify --show-snippets:false --stdin >> "%t"
// RUN: %exits-with 0 %stdin "" %baredafny verify --show-snippets:false --stdin >> "%t"
// Ensuring include statements work when processing standard in too
// (regression test for https://github.com/dafny-lang/dafny/issues/4135)
// We don't capture the output to %t because it ends up including paths,
// which are platform-dependent (i.e. "\" on Windows vs. "/" on Mac OS and Linux)
// RUN: %exits-with 4 %baredafny verify --show-snippets:false --verify-included-files --stdin < %S/Input/IncludesTuples.dfy
// RUN: %diff "%s.expect" "%t"
