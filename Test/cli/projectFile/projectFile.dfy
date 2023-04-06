// RUN: %baredafny resolve "%S/dafny.toml" > "%t"
// RUN: %diff "%s.expect" "%t"

// How do I decide if I have a toml file or a .dfy file?