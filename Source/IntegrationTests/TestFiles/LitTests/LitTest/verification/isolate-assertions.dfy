// RUN: %verify --progress --cores=1 %s &> %t.raw
// RUN: %sed 's/taking \d*ms/redacted/g' %t.raw > %t
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK-L:Verification part 1/3 of Foo, on line 10, verified successfully, redacted and consuming 8.7E+002 resources
// CHECK-L:Verification part 2/3 of Foo, on line 11, verified successfully, redacted and consuming 3.1E+003 resources
// CHECK-L:Verification part 3/3 of Foo, on line 12, verified successfully, redacted and consuming 2.8E+003 resources
// CHECK-L:Verified 1/2 symbols. Waiting for Bar to verify.
// CHECK-L:Verification part 1/1 of Bar, on line 15, verified successfully, redacted and consuming 3.1E+003 resources

method {:isolate_assertions} Foo() {
  assert true;
  assert true;
}

method Bar() {
  assert true;
  assert true;
}