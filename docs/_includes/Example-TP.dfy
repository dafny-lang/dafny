datatype Result<T> = Failure(error: string) | Success(v: T)
datatype ResultN<T(!new)> = Failure(error: string) | Success(v: T)

class C {}

method m() {
  var x1: Result<int>;
  var x2: ResultN<int>;
  var x3: Result<C>;
  var x4: ResultN<C>; // error
  var x5: Result<array<int>>;
  var x6: ResultN<array<int>>; // error
}


