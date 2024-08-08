module {:options "--function-syntax:4"} LibraryModule {

  function TimesTwo(x: nat): nat
  {
    x * 2
  }

  datatype Result<+T, +E> = Success(value: T) | Failure(error: E)

  // Record type
  datatype Pair<+T, +U> = Pair(first: T, second: U)

  datatype NestedTypeConstructorRecord<+T> = First(value: Pair<T, T>)
  datatype NestedTypeConstructorClass<+T> = First2(value: Pair<T, T>) | Second2(value: Pair<T, T>)

  datatype NoTypeArgs = Success2 | Failure2

}
