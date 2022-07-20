// RUN: %dafny /compile:0 "%refmanexamples/Example-BV2.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
