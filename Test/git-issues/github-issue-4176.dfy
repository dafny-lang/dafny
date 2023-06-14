method test() {
    var c := new Class();
    reveal Class.P();
    assert c.P();
}

class Class {
  opaque function P() : bool { true }

  constructor () { }
}
//