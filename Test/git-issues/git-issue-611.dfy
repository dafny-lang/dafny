module M1 {
  export reveals *
  export Nothing

  type T
}

module M2 {
  import M1
  import Nothing = M1`Nothing

  export provides f, M1

  function f() : M1.T
}

