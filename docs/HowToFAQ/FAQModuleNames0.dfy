module util {
  const x: nat := 0
}

module java {
  module util {
    const y: nat := util.x
    method test() { assert y == 0; }
  }
}
