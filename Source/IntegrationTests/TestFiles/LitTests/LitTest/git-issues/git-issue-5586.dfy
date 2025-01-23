// RUN: %exits-with 4 %verify --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


trait Trait { }

class Class extends Trait { }

predicate P(t: Trait) {
  t is Class // this is the related location of the error below
}

method M(u: Trait) {
  assert P(u); // error
}
