module util {
  const x: nat := 0
}

module util_ {
  import util
}

module java {
  module util {
    import util_
    const y: nat := util_.util.x
    method test() { assert y == 0; }
  }
}
