// RUN: %dafny /compile:0 "%refmanexamples/Example-Fail1.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
