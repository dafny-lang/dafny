// RUN: %dafny /compile:0 /verifyAllModules "%s" > "%t"
// RUN: ! %baredafny run %args --no-verify --target=cs /unicodeChar:1 "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=go /unicodeChar:1 "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=java /unicodeChar:1 "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=js /unicodeChar:1 "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=py "%s" /unicodeChar:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
