module Helpers {
  static function method addOne(n: nat): nat 
    ensures addOne(n) == n + 1;
  {
    n + 1
  }
}
module Mod {
  import opened Helpers;
  method m() {
    assert addOne(5) == 6;
  }
}