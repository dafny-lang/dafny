// RUN: %verify --verify-included-files "%s" > "%t"
// RUN: ! %run --no-verify --target cs "%s" >> "%t"
// RUN: ! %run --no-verify --target go "%s" >> "%t"
// RUN: ! %run --no-verify --target java "%s" >> "%t"
// RUN: ! %run --no-verify --target js "%s" >> "%t"
// RUN: ! %run --no-verify --target py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
