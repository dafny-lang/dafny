// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=full --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following tests apply only --general-traits=full, since that mode allows a newtype to both
// be based on `real` and extend traits.
// Alternatively, if newtypes could have a datatype as the base type, then these tests could be
// changed (or appended) to use --general-traits=datatype and use a datatype as the newtype base type.

trait SupportsAdd {
  function Add(x: int): int
}

newtype NonNegativeReal extends SupportsAdd = r: real | 0.0 <= r {
  function Add(x: int): int {
    Floor + x
  }
}

method Test(n: NonNegativeReal) {
  var x := n.Floor;
  var y := n.Add(x);
  if {
    case true =>
      assert y == n.Floor + n.Floor;
      assert x <= y;
    case true =>
      assert 2 * n.Floor == x + y; // error: x + y == 3 * n.Floor
    case true =>
  }

  var m: NonNegativeReal;
  if {
    case true =>
      m := (x + y) as real as NonNegativeReal;
    case true =>
      m := (y - x) as real as NonNegativeReal;
    case true =>
      m := (x - y) as real as NonNegativeReal; // error: x-y may be negative
  }
}
