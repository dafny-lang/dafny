// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo
{
  method FooMethod()  returns (r: Result<string>)
    ensures
      match r {
        case Success(()) => true // ERROR () does not match string
        case Failure(e) => true
      }

  method FooMethod2()  returns (r: Result<C>)
    ensures
      match r {
        case Success(D()) => true // ERROR - not a constructor
        case Failure(e) => true
      }

  method FooMethod3()  returns (r: Result<C>)
    ensures
      match r {
        case Success(C2()) => true // ERROR - wrong number of arguments
        case Failure(e) => true
      }

  method FooMethod5()  returns (r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true
        case Success(C1) => true // this is the same as the previous case (warning is not shown, because it is emitted post resolution)
        case Failure(e) => true
      }

  method FooMethod2q(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1()) => x := 1;
      case Success(C2(x)) => x := 2;  // error: x is not local variable
      case Failure(e) => x := 3;
    }
    assert x == 0 || x == 1 || x == 3;
    expect x == 0 || x == 1 || x == 3;
  }

  method FooMethod2r(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: real := 0.0;
    match r {
      case Success(C1()) => x := 1.0;
      case Success(C2(x)) => x := 2;  // error: x is not local variable
      case Failure(e) => x := 3.0;
    }
    assert x == 0.0 || x == 1.0 || x == 3.0;
    expect x == 0.0 || x == 1.0 || x == 3.0;
  }

  method FooMethod40(r: Result<C>)
    ensures
      match r {
        case Success(C2) => true // error: unary constructor applied without arguments
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C2) => x := 1; // error: unary constructor applied without arguments
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }

  method FooMethod41(r: Result<string>)
    ensures
      match r {
        case Success(C1) => true // OK -- C1 is a nullary constructor
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1; // OK -- C1 is a nullary constructor
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }

  method FooMethod42(r: Result<C>)
    ensures
      match r {
        case Success(C1()) => true // OK -- C1 is a nullary constructor
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1()) => x := 1; // OK -- C1 is a nullary constructor
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }

  method FooMethod50(r: Result<string>)
    ensures
      match r {
        case Success(C1) => true // OK -- C1 is a bound variable (since the type expected here is string)
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1; // OK -- C1 is a bound variable (since the type expected here is string)
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }

}
