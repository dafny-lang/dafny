// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits=datatype --general-newtypes

type Small = x: int | 0 <= x < 10

newtype NewProgram = Small | true // error: 'Small' is a bound variable here, and its type is undetermined

datatype Result =
  | NewBounce(newNext: NewProgram)
  | Done()
