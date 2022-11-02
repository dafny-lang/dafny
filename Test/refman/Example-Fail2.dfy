// RUN: %dafny /compile:0 "%refmanexamples/Example-Fail2.dfy" > "%t"
// RUN: %diff "%s.expect" "%t"
