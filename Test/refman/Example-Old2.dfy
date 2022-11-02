// RUN: %dafny /compile:0 "%refmanexamples/Example-Old2.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
