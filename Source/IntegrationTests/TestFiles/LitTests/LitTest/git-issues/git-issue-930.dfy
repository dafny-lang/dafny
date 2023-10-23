// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Result<T> = Success(value: T) | Failure(error: string)
{
  predicate IsFailure() {
    Failure?
  }
  function PropagateFailure<U>(): Result<U>
    requires Failure?
  {
    Failure(this.error)
  }
  function Extract(): T
    requires Success?
  {
    value
  }
}

class ClassA<T> {
  const s: seq<T>

  constructor (s: seq<T>) {
    this.s := s;
  }

  method Read() returns (res: Result<seq<T>>)
    ensures res.Success? ==> 1 <= |res.value|
  {
    if 1 <= |s| {
      if * {
        return Success(s);
      }
    }
    return Failure("failing");
  }

  method ReadX<U(==)>(x: U, y: U) returns (res: Result<seq<U>>)
    ensures res.Success? ==> 1 <= |res.value|
  {
    if x != y {
      return Success([x, y]);
    }
    return Failure("failing");
  }
}

// Methods M0 and M1 are the same, except that M0 gives the type of
// "numbers", whereas M1 leaves that type to be inferred. In both
// cases, it should be known that a.Read() returns a Result<seq<int>>,
// but type inference failed (now fixed) to instantiate the T in ClassA<T>, so
// a.Read() is typed as returning a Result<seq<T>>.

method M0() returns (res: Result<int>) {
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var numbers: seq<int> :- a.Read();  // fixed: once said expected Result<seq<int>>, but got Result<seq<T>>
  return Success(numbers[0]);
}

method M1() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var numbers :- a.Read();  // fixed: once said expected Result<seq<int>>, but got Result<seq<T>>
  return Success(numbers[0]);
}

// Methods P0 and P1 are like M0 and M1, but instead of using :- to
// handle the Success/Failure of a.Read(), P0 and P1 handle those
// cases explicitly. In these cases, type checking works properly.

method P0() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var result: Result<seq<int>> := a.Read();
  if result.IsFailure() {
    res := result.PropagateFailure();
    return;
  }
  var numbers := result.Extract();
  return Success(numbers[0]);
}

method P1() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var result := a.Read();
  if result.IsFailure() {
    res := result.PropagateFailure();
    return;
  }
  var numbers := result.Extract();
  return Success(numbers[0]);
}

// Methods N0 and N1 are like M0 and M1, but class a.ReadX
// instead of a.Read. This makes the type parameter of a.ReadX
// come into play.

method N0() returns (res: Result<int>) {
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var numbers: seq<int> :- a.ReadX(50, 50);  // fixed: once said got int, but expected U
  return Success(numbers[0]);
}

method N1() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var numbers :- a.ReadX(50, 50);  // fixed: once said got int, but expected U
  return Success(numbers[0]);
}

// Methods Q0 and Q1 are like N0 and N1, but without :-. For these methods,
// type checking works properly.

method Q0() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var result: Result<seq<int>> := a.ReadX(50, 50);
  if result.IsFailure() {
    res := result.PropagateFailure();
    return;
  }
  var numbers := result.Extract();
  return Success(numbers[0]);
}

method Q1() returns (res: Result<int>)
{
  var a: ClassA<int> := new ClassA([57, 58, 59]);
  var result := a.ReadX(50, 50);
  if result.IsFailure() {
    res := result.PropagateFailure();
    return;
  }
  var numbers := result.Extract();
  return Success(numbers[0]);
}

