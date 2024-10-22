// RUN: %verify --progress VerificationJobs --cores=1 %s &> %t
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK:Verified 1/2 of Foo: assertion at line 9, verified successfully \(time: .*, resource count: .*\)
// CHECK:Verified 2/2 of Foo: assertion at line 10, verified successfully \(time: .*, resource count: .*\)
// CHECK:Verified 1/2 symbols. Waiting for Bar to verify.
// CHECK:Verified 1/1 of Bar: body, verified successfully \(time: .*, resource count: .*\)

method {:isolate_assertions} Foo() {
  assert true;
  assert true;
}

method Bar() {
  assert true;
  assert true;
}
