// NONUNIFORM: multiple testing scenarios (could be split into several uniform tests)
// RUN: %verify "%s" > "%t"

// RUN: %run --no-verify --main-method Cl.Static   --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Cl.Instance --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Tr.Static   --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Static   --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Instance --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Static   --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Instance --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Static   --target cs "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Instance --target cs "%s" >> "%t"

// RUN: %run --no-verify --main-method Cl.Static   --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Cl.Instance --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Tr.Static   --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Static   --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Instance --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Static   --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Instance --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Static   --target js "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Instance --target js "%s" >> "%t"

// RUN: %run --no-verify --main-method Cl.Static   --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Cl.Instance --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Tr.Static   --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Static   --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Instance --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Static   --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Instance --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Static   --target go "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Instance --target go "%s" >> "%t"

// RUN: %run --no-verify --main-method Cl.Static   --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Cl.Instance --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Tr.Static   --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Static   --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Instance --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Static   --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Instance --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Static   --target java "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Instance --target java "%s" >> "%t"

// RUN: %run --no-verify --main-method Cl.Static   --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Cl.Instance --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Tr.Static   --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Static   --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Dt.Instance --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Static   --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Co.Instance --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Static   --target py "%s" >> "%t"
// RUN: %run --no-verify --main-method Nt.Instance --target py "%s" >> "%t"

// RUN: %diff "%s.expect" "%t"

type plural = x | 2 <= x witness 2

class Cl<X(0)> {
  var p: plural
  var c: real
  var x: X
  static method Static() { print "Cl: static\n"; }
  method Instance() { print "Cl: ", p, " ", c, " ", x, "\n"; }
}

trait Tr<X> {
  static method Static() { print "Tr: static\n"; }
}

datatype Dt<X> = Dt0(plural, X) | Dt1(real, X) {
  static method Static() { print "Dt: static\n"; }
  method Instance() { print "Dt: ", this, "\n"; }
}

codatatype Co<X> = CoMore(plural, X, Co) {
  static method Static() { print "Co: static\n"; }
  method Instance() { print "Co: ", this, "\n"; }
}

newtype Nt = x | -0x8000_0000 <= x <= 0x8000_0000 {
  const c: plural
  static method Static() { print "Nt: static\n"; }
  method Instance() { print "Nt: ", this, " ", c, "\n"; }
}
