// RUN: %verify "%s" > "%t"
// RUN: ! %run --no-verify --target cs "%s" >> "%t"
// RUN: ! %run --no-verify --target java "%s" >> "%t"
// RUN: ! %run --no-verify --target js "%s" >> "%t"
// RUN: ! %run --no-verify --target go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
   expect false;
}
