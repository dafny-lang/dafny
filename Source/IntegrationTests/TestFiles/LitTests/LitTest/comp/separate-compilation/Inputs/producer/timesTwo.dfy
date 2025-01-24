module {:options "--function-syntax:4"} CoolLibraryName {

  // Ensuring this module is not empty,
  // or else it will be omitted from the translation record.
  const FOO := 42

  module LibraryModule {

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
}

// Ensuring reserved names in some languages are escaped consistently across languages
module Math {
  function Add(x: int, y: int): int {
    x + y
  }
}