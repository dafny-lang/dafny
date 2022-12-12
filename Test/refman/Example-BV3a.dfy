// RUN: %exits-with 2 %dafny /compile:0 "%refmanexamples/Example-BV3a.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
