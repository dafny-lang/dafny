// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype S0 = S0()
datatype S1 = S1(a0: int)
datatype S2 = S2(a0: int, a1: int)
datatype S3 = S3(a0: int, a1: int, a2: int)

method Test0a(x: int) returns (s0: S0, s1: S1, s2: S2, s3: S3) {
  s0 := S0;
  s1 := S1;  // error: too few arguments
  s2 := S2;  // error: too few arguments
  s3 := S3;  // error: too few arguments
}

method Test0b(x: int) returns (s0: S0, s1: S1, s2: S2, s3: S3) {
    s0 := S0();
  s1 := S1();  // error: too few arguments
  s2 := S2();  // error: too few arguments
  s3 := S3();  // error: too few arguments
}

method Test1(x: int) returns (s0: S0, s1: S1, s2: S2, s3: S3) {
  s0 := S0(x);  // error: too many arguments
  s1 := S1(x);
  s2 := S2(x);  // error: too few arguments
  s3 := S3(x);  // error: too few arguments
}

method Test4(x: int) returns (s0: S0, s1: S1, s2: S2, s3: S3) {
  s0 := S0(x, x, x, x);  // error: too many arguments
  s1 := S1(x, x, x, x);  // error: too many arguments
  s2 := S2(x, x, x, x);  // error: too many arguments
  s3 := S3(x, x, x, x);  // error: too many arguments
}

codatatype C0 = C0()
codatatype C1 = C1(a0: int)
codatatype C2 = C2(a0: int, a1: int)
codatatype C3 = C3(a0: int, a1: int, a2: int)

method CoTest0a(x: int) returns (c0: C0, c1: C1, c2: C2, c3: C3) {
  c0 := C0;
  c1 := C1;  // error: too few arguments
  c2 := C2;  // error: too few arguments
  c3 := C3;  // error: too few arguments
}

method CoTest0b(x: int) returns (c0: C0, c1: C1, c2: C2, c3: C3) {
  c0 := C0();
  c1 := C1();  // error: too few arguments
  c2 := C2();  // error: too few arguments
  c3 := C3();  // error: too few arguments
}

method CoTest1(x: int) returns (c0: C0, c1: C1, c2: C2, c3: C3) {
  c0 := C0(x);  // error: too many arguments
  c1 := C1(x);
  c2 := C2(x);  // error: too few arguments
  c3 := C3(x);  // error: too few arguments
}

method CoTest4(x: int) returns (c0: C0, c1: C1, c2: C2, c3: C3) {
  c0 := C0(x, x, x, x);  // error: too many arguments
  c1 := C1(x, x, x, x);  // error: too many arguments
  c2 := C2(x, x, x, x);  // error: too many arguments
  c3 := C3(x, x, x, x);  // error: too many arguments
}

method ExprDotName() {
  var u := R5.x;  // error: R5 unknown
}
