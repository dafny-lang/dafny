// RUN: %run %S/run.vjava --input %S/run.dfy --input %S/__default.java --target=java > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern} out {
  newtype int32 = x: int | -0x8000_0000 <= x <= 0x7fff_ffff
  method {:extern "println" } println(value: int32)
}

// import opened Out

// method Main() {
//  println(3);
// }

// import opened Java.Lang

// method Main() {    
//   System.out.println(3);
// }

// module {:extern "java"} Java {

//   module Base {
//     newtype int32 = x: int | -0x8000_0000 <= x <= 0x7fff_ffff
//   }

//   module {:extern "lang"} Lang {
//     module {:extern} System {
//       module {:extern "externs", "" } out {
//         import opened Base
//         method {:extern "println" } println(x: int32)
//       }
//     }
//   }
// }
