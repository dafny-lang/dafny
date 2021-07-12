// RUN: %dafny /compile:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:extern} C {
  static const {:extern} IsLimit: C
}
