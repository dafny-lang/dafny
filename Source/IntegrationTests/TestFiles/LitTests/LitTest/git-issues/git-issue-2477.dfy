// RUN: %exits-with 4 %baredafny verify --show-snippets:false --use-basename-for-filename --cores:2 --verification-time-limit:300 --resource-limit:5e6 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T extends object {
  predicate P()
    reads {this}
}

class C extends T {
  predicate P() // predicate's decreases clause must be below or equal to that in the trait
  {
    true
  }
}
