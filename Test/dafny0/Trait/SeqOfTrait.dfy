
// RUN: %dafny /compile:3 /spillTargetCode:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Trait {

}

class Class extends Trait {
  constructor() {

  }
}

method Main() {
  var instance := new Class();
  var s: seq<Trait> := [instance];
}