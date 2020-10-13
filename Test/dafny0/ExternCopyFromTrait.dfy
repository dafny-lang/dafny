// RUN: %dafny /compile:1 /compileTarget:cs /print:"%t.print" /dprint:"%t.dprint" "%s" ExternCopyFromTraitLibrary.cs > "%t"
// RUN: %diff "%s.expect" "%t"
module {:extern "M"} M {
  trait {:extern} T1 {
    method {:extern "m1_ext"} m1()
  }
  class {:extern} C1 extends T1 {

    method {:extern "m1_ext_different"} m1() {
        print "";
    }
  }

  trait {:extern} T2 {
    method {:extern "m2_ext"} m2()
  }
  class {:extern} C2 extends T2 {

    method m2() {
    }
  }
}