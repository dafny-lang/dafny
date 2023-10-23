module ModA {
  const x: int := 3
  
  function TakesIdentityAndAppliesIt<T>(f: (T, T) -> T, x: T): T {
    f(x, x)
  }
  
  const tuple3 := (2,3,4)
  const tuple2 := (2,3)
  
  module FilledWithPrefixes {
  }
  
  module FilledWithPrefixes.PrefixContent {
    const x := 3 
  }
  
  module StandalonePrefix.Prefix {
    const x := 3
  }
}

module PrefixModuleInDefaultModule.Content {
  const x := 3
}

module SpreadOverMultipleFiles.Child1 {
  const x := 3
}
