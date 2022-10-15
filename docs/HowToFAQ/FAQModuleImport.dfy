module A {
  type D = string
}

module Y {
  import opened A

  module X {
    type X = D
  }

  module Z {
    type Z = D
  }
}
