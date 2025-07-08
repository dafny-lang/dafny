// RUN: ! %baredafny test %args --allow-warnings --test-assumptions=externs %s %s.externs.cs > %t
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%S/AllExterns.cs" "%s"
// CHECK: .*Foo____dafny__checked\(x\).*
// CHECK: .*Foo____dafny__checked\(new BigInteger\(3\)\).*
// CHECK: .*Bar____dafny__checked\(x\).*
// CHECK: .*Bar____dafny__checked\(new BigInteger\(3\)\).*
include "Inputs/CheckExtern.dfy"
