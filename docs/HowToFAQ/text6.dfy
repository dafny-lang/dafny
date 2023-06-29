datatype Record = Record(x: int, ghost y: int)
method m(r: Record) returns (rr: Record) {
  rr := r.(y:=43);
}
