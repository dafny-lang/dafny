// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait T {
  function method F(): int
}

class C extends T {
  method F() returns (res: int) { // error: overwrite makes a change
    res := 5;
  }
}

class C' extends T {
  function F(): int { 5 } // error: overwrite makes a change
}

class C'' extends T {
  static function method F(): int { 5 } // error: overwrite makes a change
}

trait U {
  method M() returns (res: int)
}

class D extends U {
  function method M(): int{ // error: overwrite makes a change
    5
  }
}

class D' extends U {
  ghost method M() returns (res: int) { // error: overwrite makes a change
    res := 5;
  }
}

class D'' extends U {
  lemma M() returns (res: int) { // error: overwrite makes a change
    res := 5;
  }
}

class D'3 extends U {
  static method M() returns (res: int) { // error: overwrite makes a change
    res := 5;
  }
}
