// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {
  export reveals *
  export Nothing

  type T
}

module M2 {
  import M1
  import Nothing = M1`Nothing

  export provides f, Nothing

  ghost function f() : M1.T
}

