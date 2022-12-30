// RUN: %dafny /compile:0 /verifyAllModules "%s" > "%t"
// RUN: ! %baredafny run %args --no-verify --target=cs --unicode-char "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=go --unicode-char "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=java --unicode-char "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=js --unicode-char "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=py "%s" --unicode-char "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
