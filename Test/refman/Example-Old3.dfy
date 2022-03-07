// RUN: %dafny /compile:0 "%refmanexamples/Example-Old3.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
