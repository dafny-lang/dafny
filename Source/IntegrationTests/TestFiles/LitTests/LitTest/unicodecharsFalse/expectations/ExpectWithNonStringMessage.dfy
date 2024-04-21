// RUN: %verify --verify-included-files --allow-deprecation --unicode-char false "%s" > "%t"
// RUN: ! %run --no-verify --target cs --allow-deprecation --unicode-char false "%s" >> "%t"
// RUN: ! %run --no-verify --target go --allow-deprecation --unicode-char false "%s" >> "%t"
// RUN: ! %run --no-verify --target java --allow-deprecation --unicode-char false "%s" >> "%t"
// RUN: ! %run --no-verify --target js "--allow-deprecation --unicode-char %s" >> "%t"
// RUN: ! %run --no-verify --target py --allow-deprecation --unicode-char false "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Note this is one good example of printing regressing with /unicodeChar:1
// in the name of simpler and more consistent semantics.

include "../../expectations/ExpectWithNonStringMessage.dfy"
