// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Helpers {
  export provides f, T
  type T = int
  function f(): T { 0 }
}
module Mod {
  export reveals h provides A
  import A = Helpers
  function h(): A.T { A.f() }
}
module Mod2 {
  import M = Mod
  import MA = M.A
  function j(): M.A.T { M.h() }
  function k(): MA.T { j() }
}
