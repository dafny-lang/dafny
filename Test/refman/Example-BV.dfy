// RUN: %dafny /compile:0 "%refmanexamples/Example-BV.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
