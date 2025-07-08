// NONUNIFORM: Multiple test scenarios (could be split)
// RUN: %verify "%s" > "%t"
// RUN: %run --no-verify --target cs --main-method A.B.Main "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method A.B.Main "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method A.B.Main "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method A.B.Main "%s" >> "%t"
// RUN: %run --no-verify --target cs --main-method A.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method A.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method A.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method A.C.Test "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class B {
    method Main() { print "Main\n"; }
  }
  class C {
    method Test() { print "Test\n"; }
  }
}

