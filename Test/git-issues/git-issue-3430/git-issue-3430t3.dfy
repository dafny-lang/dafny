// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const c := 10
  module A {
    const c := 20
    const A := 100 // In root module lookup, ignore non-modules
    module B {
      import opened A
      method m() {
        assert c == 30;
      }
    }
  }
}
