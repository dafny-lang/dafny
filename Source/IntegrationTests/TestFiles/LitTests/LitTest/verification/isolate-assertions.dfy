// RUN: %verify --progress --cores=1 %s &> %t
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK:Verification part 1/3 of Foo, on line 10, verified successfully \(time: .*, resource count: .*\)
// CHECK:Verification part 2/3 of Foo, on line 11, verified successfully \(time: .*, resource count: .*\)
// CHECK:Verification part 3/3 of Foo, on line 12, verified successfully \(time: .*, resource count: .*\)
// CHECK:Verified 1/2 symbols. Waiting for Bar to verify.
// CHECK:Verification part 1/1 of Bar, on line 15, verified successfully \(time: .*, resource count: .*\)


method {:isolate_assertions} Foo() {
  assert true;
  assert true;
}

method Bar() {
  assert true;
  assert true;
}
