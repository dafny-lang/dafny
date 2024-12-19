// RUN: %exits-with 4 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  export OnlySome
    provides NeedlesslyParameterizedType
  export Everything
    reveals NeedlesslyParameterizedType

  type NeedlesslyParameterizedType<X> = bool
}

module Client {
  import Library`OnlySome

  class Cell<G> {
    constructor () { }
  }

  lemma Different(xx: Cell<Library.NeedlesslyParameterizedType<int>>, yy: Cell<Library.NeedlesslyParameterizedType<real>>)
    ensures xx != yy as object
  { // error: postcondition not satisfied

    // Suppose Library.NeedlesslyParameterizedType were an injective type constructor. Then,
    //     Library.NeedlesslyParameterizedType<int>
    // and
    //     Library.NeedlesslyParameterizedType<real>
    // are different types. From this, it follows that xx and yy are are also of different types, and thus
    // xx and yy must be different objects.
    // But xx and yy could really be the same object, as demonstrated by Main below. Thus, the axiomatization
    // should not say that Library.NeedlesslyParameterizedType is injective (which it once had done).
  }
}

module Contradiction {
  import Library`Everything
  import Client

  method Main() {
    var c := new Client.Cell<bool>();
    Client.Different(c, c);
    assert false;
    print 1/0, "\n";
  }
}
