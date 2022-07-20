class P {
  twostate function F<X>(x: X): X
}

method EtaExample(p: P) returns (ghost f: int -> int) {
  label L:
  f := x => p.F<int>@L(x);
}
