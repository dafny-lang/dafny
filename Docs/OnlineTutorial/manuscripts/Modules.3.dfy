module Mod {
  module Helpers {
    class C {
      method doIt()
      var f: int;
    }
  }
  method m() {
    var x := new Helpers.C;
    x.doIt();
    x.f := 4;
  }
}