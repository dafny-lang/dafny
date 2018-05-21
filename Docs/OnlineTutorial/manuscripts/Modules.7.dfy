module Helpers {
  static function method addOne(n: nat): nat 
    ensures addOne(n) == n + 1;
  {
    n + 1
  }
}
module Mod {
  import A = Helpers;
  method m() {
    assert A.addOne(5) == 6;
  }
}