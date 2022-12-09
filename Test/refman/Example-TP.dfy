// RUN: %exits-with 2 %dafny /compile:0 "%refmanexamples/Example-TP.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
