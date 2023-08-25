// RUN: %exits-with 4 %verify --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box<T> {
  var x: T

  constructor(x: T)
    reads {}
  {
    this.x := x;
  }
}

class Concurrent {

  function {:concurrent} GoodFn(b: Box<int>): int {
    42
  }

  function {:concurrent} BadFn(b: Box<int>): int  // Error: reads clause might not be empty ({:concurrent} restriction)
    reads b
  {
    b.x
  }

  function {:concurrent} WeirdButOkayFn(b: Box<int>): int 
    reads if false then {b} else {}
  {
    42
  }

  method {:concurrent} GoodM(b: Box<int>) {
  }

  method {:concurrent} BadM(b: Box<int>)  // Error: reads clause might not be empty ({:concurrent} restriction)
    reads b
  {
    var x := b.x;
  }

  method {:concurrent} WeirdButOkayM(b: Box<int>) 
    reads if false then {b} else {}
  {
  }

  method {:concurrent} AlsoBadM(b: Box<int>)  // Error: modifies clause might not be empty ({:concurrent} restriction)
    modifies b
  {
    b.x := 42;
  }

  method {:concurrent} AlsoWeirdButOkayM(b: Box<int>) 
    modifies if false then {b} else {}
  {
  }
}
