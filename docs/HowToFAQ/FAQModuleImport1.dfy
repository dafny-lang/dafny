module A {
  type D = string
}

module Y {

  module X {
    import opened A
    type X = D
  }

  module Z {
    import opened A
    type Z = D
  }
}
