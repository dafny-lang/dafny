// RUN: %exits-with 4 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  class Cell {
    var data: int
    constructor (data: int) {
      this.data := data;
    }
  }

  class Bell {
    var data: int
    constructor (data: int) {
      this.data := data;
    }
  }
}

abstract module Abstract {
  // Here are two abstract imports
  import X: A
  import Y: A
  import AA = A

  class Cell {  // local Cell
    var data: int
  }

  // X.Cell and Y.Cell may denote the same type
  method M0(x: X.Cell, y: Y.Cell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // error
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // error
    }
  }

  // X.Cell and X.Bell are known to be different
  method M1(x: X.Cell, y: X.Bell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // fine
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // fine
    }
  }

  // X.Cell and Y.Bell are known to be different
  method M2(x: X.Cell, y: Y.Bell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // fine
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // fine
    }
  }

  // X.Cell and AA.Cell may refer to the same type
  method M3(x: X.Cell, y: AA.Cell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // error
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // error
    }
  }

  // X.Bell and AA.Cell are known to be different
  method M4(x: X.Bell, y: AA.Cell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // fine
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // fine
    }
  }

  // X.Cell and Cell always denote different types, because there's no way to
  // concretize Abstract.X with Abstract. However, these kinds of
  // cannot-be-concretized-by relations are not encoded in the verifier, so
  // the verifier generates spurious errors in this method. A workaround is
  // to name the local class Cell something else; for example, see module
  // Abstract' below.
  method M5(x: X.Cell, y: Cell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // error
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // error
    }
  }
}

// This module just goes to show that Abstract's X and Y can indeed be concretized
// to be the same module.
module Same refines Abstract {
  import X = A
  import Y = A
}

abstract module Abstract' {
  // Here are two abstract imports
  import X: A
  import Y: A

  // Here, the local class is named Cell', so it couldn't possibly be the same
  // as the class X.Cell. Even with the local type synonym Cell, the verifier
  // does not flinch.
  type Cell = Cell'
  class Cell' {
    var data: int
  }

  // See comment in Abstract.M5 above. Here, X.Cell and Cell are known
  // to be different (because X.Cell and Cell' are known to be different).
  method M5(x: X.Cell, y: Cell)
    modifies x
  {
    if * {
      assert x != var o: object := y; o;  // fine
    } else {
      x.data := x.data + 1;
      assert y.data == old(y.data);  // fine
    }
  }
}
