module Mod {
  module Helpers {
    static function method addOne(n: nat): nat {
      n + 1
    }
  }
  method m() {
    var x := 5;
    x := Helpers.addOne(x);
    assert x == 6; // this doesn't work
  }
}