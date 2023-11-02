// RUN: %testDafnyForEachResolver --refresh-exit-code=2 "%s"

trait Trait { }
class Class extends Trait { }

method M(c: Class) {
  var t: Trait := c;
  var d: Class := t; // error: needs an "as Class" in refresh resolver
}
