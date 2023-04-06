// RUN: %baredafny resolve "%S/dafny.toml" > "%t"
// RUN: ! %baredafny resolve "%S/brokenDafny.toml" 2>> "%t"
// RUN: ! %baredafny resolve "%S/doesNotExist.toml" 2>> "%t"
// RUN: %diff "%s.expect" "%t"

// How do I decide if I have a toml file or a .dfy file?