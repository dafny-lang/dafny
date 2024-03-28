// RUN: %verify --verify-included-files "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 --target cs /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target go /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target java /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target js /unicodeChar:1 "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target py /unicodeChar:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
