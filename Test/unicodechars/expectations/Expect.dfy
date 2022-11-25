// RUN: %baredafny run --target=cs --unicode-char %args "%s" > "%t" || true
// RUN: %baredafny run --target=go --unicode-char %args "%s" >> "%t" || true
// RUN: %baredafny run --target=java --unicode-char %args "%s" >> "%t" || true
// RUN: %baredafny run --target=js --unicode-char %args "%s" >> "%t" || true
// RUN: %baredafny run --target=py --unicode-char %args "%s" >> "%t" || true
// RUN: %diff "%s.expect" "%t"
include "../../expectations/Expect.dfy"
