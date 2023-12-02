// RUN: %exits-with 4 %baredafny verify --use-basename-for-filename --show-snippets false --reads-clauses-on-methods "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Box<T> {
  var x: T

  constructor(x: T)
    reads {}
  {
    this.x := x;
  }
}

class GhostBox<T> {
  ghost var x: T

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

  function {:concurrent} BadFn(b: Box<int>): int  // Error: reads clause could not be proved to be empty ({:concurrent} restriction)
    reads b
  {
    b.x
  }

  function {:concurrent} WeirdButOkayFn(b: Box<int>): int 
    reads if false then {b} else {}
  {
    42
  }

  function {:concurrent} SurprisingButAlsoOkayFn(b: Box<int>): int 
    reads if false then {b} else {}`x
  {
    42
  }

  method {:concurrent} GoodM(b: Box<int>) {
  }

  method {:concurrent} BadMDefaultReads(b: Box<int>)  // Error: reads clause could not be proved to be empty ({:concurrent} restriction)
  {
  }

  method {:concurrent} BadM(b: Box<int>)  // Error: reads clause could not be proved to be empty ({:concurrent} restriction)
    reads b
  {
    var x := b.x;
  }

  method {:concurrent} WeirdButOkayM(b: Box<int>) 
    reads if false then {b} else {}
  {
  }

  method {:concurrent} AlsoBadM(b: Box<int>)  // Error: modifies clause could not be proved to be empty ({:concurrent} restriction)
    modifies b
  {
    b.x := 42;
  }

  method {:concurrent} AlsoWeirdButOkayM(b: Box<int>) 
    modifies if false then {b} else {}
  {
  }

  ghost method {:concurrent} OnlyReadsGhostState(b: GhostBox<int>) returns (r: int) 
    reads b`x  // Error: modifies clause could not be proved to be empty ({:concurrent} restriction)
  {
    return b.x;
  }

  method {:concurrent} OnlyModifiesGhostState(b: GhostBox<int>) 
    reads {}  // Error: reads clause could not be proved to be empty ({:concurrent} restriction)
    modifies b`x
  {
    b.x := 42;
  }

  ghost method {:concurrent} AllTheBoxes() 
    reads set b: GhostBox<int> | true  // Error: reads clause could not be proved to be empty ({:concurrent} restriction)
    modifies set b: GhostBox<int> | true  // Error: modifies clause could not be proved to be empty ({:concurrent} restriction)
  {
  }

  ghost method {:concurrent} NoneOfTheBoxes() 
    reads set b: GhostBox<int> | !allocated(b)
    modifies set b: GhostBox<int> | !allocated(b)
  {
  }
}
