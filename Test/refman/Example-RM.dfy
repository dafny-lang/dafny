// RUN: %dafny /compile:0 "%refmanexamples/Example-RM.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
