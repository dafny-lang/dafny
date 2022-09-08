// RUN: %dafny /compile:0 /countVerificationErrors:0 '/verificationLogger:csv;log.csv' "%s" > "%t
// RUN: %diff %s.expect %t
