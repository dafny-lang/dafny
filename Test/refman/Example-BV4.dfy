// RUN: %dafny_0 /compile:0 "%refmanexamples/Example-BV4.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
