// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype Result<T> =
  | Success(value: T)
  | Failure(error: string)

datatype C = C1 | C2(x: int)

trait Foo
{
  method FooMethod1(r: Result<()>)
    ensures
      match r {
        case Success(()) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(()) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
  method FooMethod2(r: Result<C>)
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
      case Success(C2(_)) => x := 2;
      case Failure(e) => x := 3;
    }
    assert x > 0;
    expect x == 1;
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
      case Success(C2(xx)) => var y := xx;
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
      case Success(C2(xx)) =>  var y := xx;
      case Failure(e) => x := 3.0;
    }
    assert x == 0.0 || x == 1.0 || x == 3.0;
    expect x == 0.0 || x == 1.0 || x == 3.0;
  }
  method FooMethod3(r: Result<C>)
    ensures
      match r {
        case Success(C1) => true // OK
        case Success(C2(x)) => true // OK
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1;
      case Success(C2(_)) => x := 2;  // BUG - problem if _ is x
      case Failure(e) => x := 3;
    }
    assert x > 0;
    expect x == 1;
  }
  method FooMethod4(r: Result<C>)
    ensures
      match r {
        case Success(C2x) => true
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C2x) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
  method FooMethod5(r: Result<string>)
    ensures
      match r {
        case Success(C1) => true // OK -- C1 is a variable
        case Failure(e) => true
      }
  {
    var x: int := 0;
    match r {
      case Success(C1) => x := 1;
      case Failure(e) => x := 2;
    }
    assert x > 0;
    expect x == 1;
  }
}

class CL extends Foo {}

method Main() {
  var t := new CL;
  m(t);
}

method m(t: Foo) {
  t.FooMethod1(Result.Success(()));
  t.FooMethod2(Result<C>.Success(C1));
  t.FooMethod2q(Result<C>.Success(C1));
  t.FooMethod2r(Result<C>.Success(C1));
  t.FooMethod3(Result<C>.Success(C1));
  t.FooMethod4(Result<C>.Success(C1));
  t.FooMethod5(Result<string>.Success(""));
  print "Done\n";
}
