// RUN: %dafny /ironDafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Delicious {}
module Chocolate exclusively refines Delicious {}
module Strawberry exclusively refines Delicious {}
