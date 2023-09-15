// RUN: %exits-with 4 %dafny /compile:0 /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Cell {
  var data: int
  constructor () {
    data := 4;
  }
}

method Main() {
  FromNew();
  FromLocalVariable();
  var c := new Cell();
  FromParameter(c);
  WithNull();
  FromMethodCall();
}

method FromNew() {
  var s := 0;
  var c := new Cell();
  for i := 0 to 3
  {
    s := s + c.data;
    c := new Cell();
  }
  print s, "\n";
}

method FromLocalVariable() {
  var cc := new Cell();
  var s := 0;
  var c := cc;
  for i := 0 to 3
  {
    s := s + c.data;
    c := cc;
  }
  print s, "\n";
}

method FromParameter(cc: Cell) {
  var s := 0;
  var c := cc;
  for i := 0 to 3
  {
    s := s + c.data;
    c := cc;
  }
  print s, "\n";
}

method WithNull() {
  var cc := new Cell();
  var s := 0;
  var c := cc;
  for i := 0 to 3
  {
    s := s + c.data; // error: c may be null
    c := null;
    c := cc;
  }
  print s, "\n";
}

method FromMethodCall() {
  var s := 0;
  var c := GetCell();
  for i := 0 to 3
  {
    s := s + c.data;
    c := GetCell();
  }
  print s, "\n";
}

method GetCell() returns (c: Cell) {
  c := new Cell();
}
