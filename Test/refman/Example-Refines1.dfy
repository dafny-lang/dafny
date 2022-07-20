// RUN: %dafny /compile:0 "%refmanexamples/Example-Refines1.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
