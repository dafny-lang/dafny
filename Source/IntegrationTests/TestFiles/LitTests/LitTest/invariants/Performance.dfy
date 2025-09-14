// RUN: %baredafny measure-complexity --type-system-refresh --check-invariants --show-snippets false --use-basename-for-filename --isolate-assertions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class HasInvariant {
  var valid: bool
  invariant valid
  constructor() {
    valid := true;
  }
}
class HasNoInvariant {
  var valid: bool
}

method processHasInvariant(h: HasInvariant) {
  useInvariant(h);
}

method useInvariant(h: HasInvariant) {
  assert h.valid;
}

method processHasNoInvariant(h: HasNoInvariant) {
  useHasNoInvariant(h);
}

method useHasNoInvariant(h: HasNoInvariant) {}
