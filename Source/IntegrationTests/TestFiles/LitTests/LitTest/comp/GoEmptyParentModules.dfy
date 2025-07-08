// RUN: %baredafny translate go %args %s
// RUN: %OutputCheck --file-to-check %S/GoEmptyParentModules-go/src/GoEmptyParentModules.go "%s"
// CHECK-NOT: "A"
// CHECK-NOT: "A_B"

module A.B.C {
  method Main() {
    print "Hi there!\n";
  }
}