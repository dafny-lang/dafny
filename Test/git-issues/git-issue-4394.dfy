// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(
    f:map<nat,nat>
) {
    const Keys := f.Keys // no problem if another name is used for the constant
}

class C {
  const Keys: set<nat>

  constructor(f:map<nat,nat>) {
    this.Keys := f.Keys;
  }
}