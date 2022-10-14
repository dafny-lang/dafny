// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"


datatype Cell<T> = Cell(value: T)

const X := 1
method q() {
  var c: Cell;  // note, type argument omitted; it will eventually be inferred
  match c {
    case Cell(X) => assert X == 1; // at this time, the type argument hasn't yet been inferred, but X is a const so it is not a variable
    case Cell(_) =>     // if X is a const, then this case is not redundant
  }
}
