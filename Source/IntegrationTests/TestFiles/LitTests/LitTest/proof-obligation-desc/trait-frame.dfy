// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  method M()
  function F(): bool
}

class C extends T {
  method M() modifies this
  function F(): bool reads this
}
