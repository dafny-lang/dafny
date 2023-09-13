// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M0 {
  ghost function F(): int { 5 }
  ghost predicate P() { true }
}
module M1 refines M0 {
  ghost function F... { 7 }  // error: not allowed to change body
  ghost predicate P... { true }  // error: not allowed to extend body
}
