// RUN: ! %dafny /compile:4 /noVerify /runAllTests:1 /testContracts:TestedExterns %s %s.externs.cs > %t
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/TestedExterns.cs" "%s"
// CHECK-NOT: .*Foo____dafny__checked\(x\).*
// CHECK: .*Foo____dafny__checked\(new BigInteger\(3\)\).*
// CHECK-NOT: .*Bar____dafny__checked\(x\).*
// CHECK: .*Bar____dafny__checked\(new BigInteger\(3\)\).*
include "Inputs/CheckExtern.dfy"

method {:extern} NotCalled(x: int) returns (y: int)
  ensures y != x
