// RUN: %tobinary %s > %t.assertFalse.dbin
// RUN: %verify --input-format Binary %S/Inputs/additional.dfy --stdin < %t.assertFalse.dbin > %t
// RUN: %diff "%s.expect" "%t"

class Anything {
  const x := 3123.012314
}
