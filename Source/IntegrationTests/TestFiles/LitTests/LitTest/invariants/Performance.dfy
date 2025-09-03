// RUN: %verify --type-system-refresh --check-invariants --performance-stats=1 "%s" > "%t"
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
