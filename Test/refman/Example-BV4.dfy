// RUN: %exits-with 4 %dafny /compile:0 "%refmanexamples/Example-BV4.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
