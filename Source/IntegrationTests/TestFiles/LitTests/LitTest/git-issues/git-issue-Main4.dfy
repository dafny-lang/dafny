// NONUNIFORM: Multiple test scenarios (could be split)
// RUN: %verify "%s" > "%t"
// RUN: %run --no-verify --target cs --main-method A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method A.AA.Test "%s" >> "%t"
// RUN: %run --no-verify --target cs --main-method B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method B.C.Test "%s" >> "%t"
// RUN: %run --no-verify --target cs --main-method B.Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method B.Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method B.Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method B.Test "%s" >> "%t"
// RUN: %run --no-verify --target cs --main-method Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method Test "%s" >> "%t"
// RUN: %run --no-verify --target cs --main-method C.Test "%s" >> "%t"
// RUN: %run --no-verify --target js --main-method C.Test "%s" >> "%t"
// RUN: %run --no-verify --target go --main-method C.Test "%s" >> "%t"
// RUN: %run --no-verify --target java --main-method C.Test "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target cs --main-method X "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target js --main-method X "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target go --main-method X "%s" >> "%t"
// RUN: %exits-with 3 %run --no-verify --target java --main-method X "%s" >> "%t"

module A {
  module AA {
    method Test() { print "Test1\n"; }
  }
}

module B {
  class C {
    static method Test() { print "Test2\n"; }
  }
  method Test() { print "Test3\n"; }
}

method Test() { print "Test4\n"; }

class C {
  static method Test() { print "Test5\n"; }
}
