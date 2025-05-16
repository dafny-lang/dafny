// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %resolve --check-source-location-consistency --input-format Binary %S/Inputs/additional.dfy --allow-warnings --stdin < %t.assertFalse.dbin > %t
// RUN: ! %resolve --check-source-location-consistency --input-format Binary --allow-warnings --stdin < %S/Inputs/inputFormat.incorrectSourceLocation.dbin >> %t
// RUN: %diff "%s.expect" "%t"

class Anything {
  const x := 3123.012314

  method foo() {
    while(true) {
      continue;
    }
    assert(old(this) == this);
    assert(unchanged(this));
    assert(fresh(this));
  }
}
