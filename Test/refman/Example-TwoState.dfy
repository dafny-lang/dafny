// RUN: %dafny_0 /verifyAllModules /compile:0 "%refmanexamples/Example-TwoState.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
