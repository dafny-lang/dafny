// RUN: %dafny /compile:4 /noVerify /runAllTests:1 /testContracts:Externs %s %s.externs.cs > %t
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/AllExterns.cs" "%s"
// CHECK: .*Foo____dafny__checked\(x\).*
// CHECK: .*Foo____dafny__checked\(new BigInteger\(3\)\).*
// CHECK: .*Bar____dafny__checked\(x\).*
// CHECK: .*Bar____dafny__checked\(new BigInteger\(3\)\).*
include "Inputs/CheckExtern.dfy"
