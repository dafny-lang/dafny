// RUN: %dafny /compile:4 /noVerify /runAllTests:1 /testContracts:ExternsInTests %s %s.externs.cs > %t
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/ExternsInTests.cs" "%s"
// CHECK-NOT: .*Foo__checked\(x\).*
// CHECK: .*Foo__checked\(new BigInteger\(3\)\).*
// CHECK-NOT: .*Bar__checked\(x\).*
// CHECK: .*Bar__checked\(new BigInteger\(3\)\).*
include "CheckExtern.dfy"
