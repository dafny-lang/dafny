// RUN: %dafny /compile:0 /verifyAllModules "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:cs /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:go /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:java /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:js /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:py /unicodeChar:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
