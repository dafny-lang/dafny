// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const c := 10
  module A {
    const c := 20
    module A {
      const c := 30
      module A {
        const c := 50
      }
    }
    module B {
      import opened A
      method m() {
        assert c == 30;
      }
    }
  }
}
