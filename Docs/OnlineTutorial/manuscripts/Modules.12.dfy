module Interface {
  static function method addSome(n: nat): nat 
    ensures addSome(n) > n;
}
module Mod {
  import A as Interface;
  method m() {
    assert 6 <= A.addSome(5);
  }
}
module Implementation {
  static function method addSome(n: nat): nat 
    ensures addSome(n) == n + 1;
  {
    n + 1
  }
}
module Mod2 refines Mod {
  import A = Implementation;
  method m() {
    ...;
    // this is now provable, because we know A is Implementation
    assert 6 == A.addSome(5);
  }
}