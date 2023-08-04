// RUN: %exits-with 1 %dafny /compile:0 '/verificationLogger:csv;log.csv' "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
