// RUN: %exits-with 4 %dafny /verifyAllModules /compile:0 "%refmanexamples/Example-TwoState.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
