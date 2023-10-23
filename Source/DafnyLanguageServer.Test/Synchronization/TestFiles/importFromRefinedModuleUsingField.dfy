module Library {
    datatype Datatype = True | False
}

module Refined {
  import opened Library
}

module Refiner refines Refined {
  function Foo(dt: Datatype) : int 
  {
    if (dt.True?) then 3 else 2
  }
}