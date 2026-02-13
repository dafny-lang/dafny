// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


type pos = x | 1 <= x witness 3

method ImplicitConversions(f: bool ~> nat) {
  var g: bool ~> int := f;
  var h: bool ~> pos := f; // error (case in point: f(true) may be 0)
}

method CompareRegression(f: bool ~> nat) {
  var g := f as bool ~> int;
  var h := f as bool ~> pos; // error (case in point: f(true) may be 0)
}

// regression test:

trait TT {}
datatype Data extends TT = CreateData
type JustData = t: TT | t is Data witness *

method Test0(dd: Data) returns (jd: JustData) {
  // the translation of the following line once generated malformed Boogie (missing Box(...))
  jd := dd as JustData;
}

method Test1(tt: TT) returns (jd: JustData)
  requires tt is Data
{
  jd := tt as JustData;
}
