// RUN: %dafny_0 /compile:0 "%refmanexamples/Example-BV.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
