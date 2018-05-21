module Helpers {
  static function method addOne(n: nat): nat 
    ensures addOne(n) == n + 1;
  {
    n + 1
  }
}
module Mod {
  import opened Helpers;
  function addOne(n: nat): nat {
    n - 1
  }
  method m() {
    assert addOne(5) == 6; // this is now false,
                           // as this is the function just defined
    assert Helpers.addOne(5) == 6; // this is still true
  }
}