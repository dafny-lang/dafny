// RUN: %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype T = T(
    f:map<nat,nat>
) {
    const Keys := f.Keys // Used to be an error
}

codatatype codatatypeT = CT(
    f:map<nat,nat>
) {
    const Keys := f.Keys // Used to be an error
}

type opaqueT {
  const f: map<nat, nat>
  const Keys := f.Keys
}

newtype newT = x: int | true {
  const f: map<nat, nat> := map[]
  const Keys := f.Keys
}

class C {
  const Keys: set<nat>

  constructor(f:map<nat,nat>) {
    this.Keys := f.Keys;
  }
}