// RUN: %run --target=java "%s" --input %S/__default.java > "%t"
// RUN: %diff "%s.expect" "%t"

import opened Java.Lang

method Main() {    
  System.out.println(3);
}

module {:extern "java"} Java {

  module Base {
    newtype int32 = x: int | -0x8000_0000 <= x <= 0x7fff_ffff
  }

  module {:extern "lang"} Lang {
    module {:extern} System {
      module {:extern "externs", "" } out {
        import opened Base
        method {:extern "println" } println(x: int32)
      }
    }
  }
}
