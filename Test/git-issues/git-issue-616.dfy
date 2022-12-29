// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module TestBad2 {
  export Abs provides D1, D1.constTest

  datatype D1<T> = D1(o : T)
  {
    const constTest := true
  }

}

module TestBad3 {
  import TestBad2`Abs

  method test(qa : TestBad2.D1<int>) {}
}

