// RUN: %run --target go "%s" > %t
// RUN: %diff "%s.expect" "%t"

module {:extern} ExternModule {
    method {:extern} TestA() returns (s: string)

    method B() {
        var a := TestA();
    }
}

import opened ExternModule
method Main() {
   B();
   print "hello";
}