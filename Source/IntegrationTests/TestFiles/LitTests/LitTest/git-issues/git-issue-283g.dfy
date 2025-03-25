// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Main {
  datatype Result<T> =
    | Success(value: T)
    | Failure(error: string)

  datatype Bar = C1() | C2(bl: string)

  const X: int := 42
  const SS: string := "asd"

  trait Foo
  {
    static const S: string := "asd"

    method FooMethod1() returns (r: Result<string>)
      ensures
        match Result<string>.Failure(S) {
          case Failure(X) => true  // ERROR: X is a constant, but wrong type
          case Success(C1) => true // C1 is a variable
        }

  }

  datatype Cell<T> = Cell(value: T)

  const Y := 1  // type of Y must be inferred
  method q() {
    var c: Cell;  // note, type argument omitted; it will eventually be inferred
    match c {
      case Cell(Y) =>
      case Cell(_) =>     // if Y is a const, then this case is not redundant
    }
    c := Cell(1.2); // ERROR: 1.2 is real, which doesn't agree with the inferred type Cell<int> of c
  }

  method qq() {
    var c: Cell<real>;
    match c {
      case Cell(Y) =>     // ERROR: Y is a const int, so a type mismatch is reported
      case Cell(_) =>     // if Y is a const, then this case is not redundant
    }
  }

  method qqq() {
    var c: Cell;
    match c {
      case Cell(XX: int) =>    // XX is a variable (there's a subtle point here, see SubtlePoint module below)
      case Cell(_) =>     // redundant case warning not shown because it's created post resolution
    }
  }
}

module SubtlePoint {
  // Methods Example0 and Example1 below differ only in where the assignment "c := Cell(Another);" takes place.
  //
  // In Example0, the assignment is placed before the "match". So, by the time the resolver looks at the "match",
  // it knows the type of "c" is "Cell<Way>". This lets the resolver look up "One" in type "Way" and can then
  // determine that "One" denotes a constructor. (And in Example2, that lookup finds that "one" is not a
  // constructor.)
  //
  // In Example1, the resolver looks at the "match" before it knows enough of the type of
  // "c" to determine a type for the argument in "case Cell(...)". Thus, the resolver does not know
  // (at the time it's looking at the "match") if the argument is a variable or a literal.
  // The resolver thus reports an error, complaining that it doesn't know enough about the type
  // of "c" when looking at the "match".
  //
  // A variation of Example1 is Example3 (and also method qqq above), where the argument is given as an explicit
  // type. That says that the argument to the Cell constructor is to be a variable.
  //
  // Yet another variation of Example1 is Example4, where the argument in the pattern is "_". That also makes it
  // clear that the programs wants a(n anonymous) variable, so no error is reported.
  //
  // Reflection: These subtleties stem from the old design in Dafny of using the enclosing type when looking up
  // resolving pieces of case patterns. It would be good to change this design so that each piece of a pattern
  // could be resolved without needing to know the enclosing type. When that change eventually makes it into the
  // language, then the outcome of these tests will change.
  //
  // Note: The legacy resolver treats "One" as a variable in both Example0 and Example2. That looks good at first,
  // because it means the type argument of the type of "c" is not needed. However, if the type of "c" is
  // explicitly given as "Cell<Way>", then the legacy resolver treat "One" as a constructor. That seems worse.
  // The new resolver at least behaves consistently (for programs that do pass the resolver), regardless of when
  // or how the full type information of "c" is obtained.
  //
  // A future improvement of the resolver would be to delay looking at the "match" until enough type information
  // has been inferred. This would mean that Example1 would no longer give an error, but would behave just like
  // Example0.

  datatype Cell<T> = Cell(value: T)
  datatype Way = One | Another

  method Example0() {
    var c: Cell;
    c := Cell(Another);
    match c { // fine, the type of "c" is known, so the "One" on the next line is known to denote the Way.One constructor
      case Cell(One) =>
    }
  }

  method Example1() {
    var c: Cell;
    match c { // error: type of c is not sufficiently resolved by this time
      case Cell(One) =>
    }
    c := Cell(Another);
  }

  method Example2() {
    var c: Cell;
    c := Cell(Another);
    match c { // fine, the type of "c" is known, so the "one" on the next line is known not to denote any Way constructor
      case Cell(one) =>
    }
  }

  method Example3() {
    var c: Cell;
    match c { // fine, because the explicit type annotation ": Way" on the next line says that "One" is to be a variable
      case Cell(One: Way) =>
    }
    c := Cell(Another);
  }

  method Example4() {
    var c: Cell;
    match c { // no error, since the type argument of "Cell" is not needed in "case Cell(_)"
      case Cell(_) =>
    }
    c := Cell(Another);
  }
}
