// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Module {
  module M {
    const {:opaque} Five := 5
  }

  method Test() {
    if * {
      assert M.Five == 5; // error: this is not known here
    } else {
      reveal M.Five;
      assert M.Five == 5;
    }
  }
}

module Class {
  class Class {
    const {:opaque} Five := 5
  }

  method Test(c: Class) {
    if * {
      assert c.Five == 5; // error: this is not known here
    } else {
      reveal c.Five;
      assert c.Five == 5;
    }
  }
}

module TypeMembers {
  trait Tr {
    const fav: bool
    const {:opaque} IsFavorite := fav
    static const {:opaque} Five := 5
  }

  datatype Color = Carrot | Pumpkin
  {
    const {:opaque} IsFavorite := this == Pumpkin
    static const {:opaque} Five := 5
  }

  newtype Small = x | 30 <= x < 40 witness 30
  {
    const {:opaque} IsFavorite := this == 34
    static const {:opaque} Five := 5
  }

  method Test(tr: Tr, c: Color, s: Small) {
    if
    case tr.IsFavorite =>
      assert tr.fav;  // error: this is not known here
    case c.IsFavorite =>
      assert c == Pumpkin;  // error: this is not known here
    case s.IsFavorite =>
      assert s == 34;  // error: this is not known here
    case tr.IsFavorite =>
      reveal tr.IsFavorite;
      assert tr.fav;
    case c.IsFavorite =>
      reveal c.IsFavorite;
      assert c == Pumpkin;
    case s.IsFavorite =>
      reveal s.IsFavorite;
      assert s == 34;
    case true =>
      if tr.IsFavorite && c.IsFavorite && s.IsFavorite {
        reveal tr.IsFavorite, c.IsFavorite, s.IsFavorite;
        assert !tr.fav || c == Carrot || s == 39;  // error: not true
      }
  }

  ghost function IsUneven(i: int): bool { i % 2 == 1 }

  method StaticTest() {
    if
    case IsUneven(Tr.Five) =>
      assert Tr.Five == 5;  // error: this is not known here
    case IsUneven(Color.Five) =>
      assert Color.Five == 5;  // error: this is not known here
    case IsUneven(Small.Five) =>
      assert Color.Five == 5;  // error: this is not known here
    case IsUneven(Tr.Five) =>
      reveal Tr.Five;
      assert Tr.Five == 5;
    case IsUneven(Color.Five) =>
      reveal Color.Five;
      assert Color.Five == 5;
    case IsUneven(Small.Five) =>
      reveal Small.Five;
      assert Small.Five == 5;
    case true =>
      if IsUneven(Tr.Five) && IsUneven(Color.Five) && IsUneven(Small.Five) {
        reveal Tr.Five, Color.Five, Small.Five;
        assert Tr.Five != 5 || Color.Five != 5 || Small.Five != 5;  // error: not true
      }
  }
}
