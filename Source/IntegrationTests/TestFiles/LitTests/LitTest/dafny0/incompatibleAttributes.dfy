// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:rlimit 10} {:resource_limit 10000} M() {
  assert true;
}
