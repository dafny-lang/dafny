// RUN: %dafny /compile:0 "%refmanexamples/Example-Old.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
