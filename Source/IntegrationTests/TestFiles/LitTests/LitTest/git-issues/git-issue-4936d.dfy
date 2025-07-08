// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits:datatype

module X {
  export Public
    provides A
  export Friends
    reveals A

  trait {:termination false} A extends object {}
}

module Y0 {
  import opened X`Public

  trait B extends A { // error: A is not even known to be a trait
    function GetIndex(): nat
      reads this
  }
}

module Y1 {
  import opened X`Friends

  trait B extends A {
    function GetIndex(): nat
      reads this // fine, since B is known to be a reference type
  }
}

module Y2 {
  import opened I = X`Friends
  import opened J = X`Public

  trait B extends A {
    function GetIndex(): nat
      reads this // fine, since B is known to be a reference type
  }
}

module Y3 {
  import opened X`Friends
  import opened J = X`Public

  trait B extends J.A { // fine, since the module also imports X`Friends
    function GetIndex(): nat
      reads this // fine, since B is known to be a reference type
  }
}

module Y4 {
  import I = X`Friends
  import J = X`Public

  trait B extends J.A { // fine, since the module also imports X`Friends
    function GetIndex(): nat
      reads this // fine, since B is known to be a reference type
  }
}
