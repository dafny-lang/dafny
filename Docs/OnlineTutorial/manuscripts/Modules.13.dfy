module Interface {
  static function method addSome(n: nat): nat 
    ensures addSome(n) > n;
}
module Mod {
  import A as Interface default Implementation;
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