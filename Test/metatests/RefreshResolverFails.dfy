// RUN: %testDafnyForEachResolver "%s" --refresh-exit-code=2

trait Trait { }
class Class extends Trait { }

method M(c: Class) {
  var t: Trait := c;
  var d: Class := t; // error: needs an "as Class" in refresh resolver
}
