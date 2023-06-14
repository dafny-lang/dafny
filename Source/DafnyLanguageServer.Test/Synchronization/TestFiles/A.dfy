module ModA {
  const x: int := 3
  
  function TakesIdentityAndAppliesIt<T>(f: (T, T) -> T, x: T): T {
    f(x, x)
  }
}
