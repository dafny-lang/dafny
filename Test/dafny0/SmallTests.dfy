class Node {
  var next: Node;

  function IsList(r: set<Node>): bool
    reads r; 
  {
    this in r &&
    (next != null  ==>  next.IsList(r - {this}))
  }

  method Test(n: Node, nodes: set<Node>) 
  {
    assume nodes == nodes - {n};
    // the next line needs the Set extensionality axiom, the antecedent of
    // which is supplied by the previous line
    assert IsList(nodes) == IsList(nodes - {n});
  }

  method Create()
    modifies this;
  {
    next := null;
    var tmp: Node;
    tmp := new Node;
    assert tmp != this;  // was once a bug in the Dafny checker
  }

  method SequenceUpdateOutOfBounds(s: seq<set<int>>, j: int) returns (t: seq<set<int>>)
  {
    t := s[j := {}];  // error: j is possibly out of bounds
  }

  method Sequence(s: seq<bool>, j: int, b: bool, c: bool) returns (t: seq<bool>)
    requires 10 <= |s|;
    requires 8 <= j && j < |s|;
    ensures |t| == |s|;
    ensures t[8] == s[8] || t[9] == s[9];
    ensures t[j] == b;
  {
    if (c) {
      t := s[j := b];
    } else {
      t := s[..j] + [b] + s[j+1..];
    }
  }

  method Max0(x: int, y: int) returns (r: int)
    ensures r == (if x < y then y else x);
  {
    if (x < y) { r := y; } else { r := x; }
  }

  method Max1(x: int, y: int) returns (r: int)
    ensures r == x || r == y;
    ensures x <= r && y <= r;
  {
    r := if x < y then y else x;
  }

  function PoorlyDefined(x: int): int
    requires if next == null then 5/x < 20 else true;  // ill-defined then branch
    requires if next == null then true else 0 <= 5/x;  // ill-defined then branch
    requires if next.next == null then true else true;  // ill-defined guard
    requires 10/x != 8;  // this is well-defined, because we get here only if x is non-0
    reads this;
  {
    12
  }
}

// ------------------ modifies clause tests ------------------------

class Modifies {
  var x: int;
  var next: Modifies;

  method A(p: Modifies)
    modifies this, p;
  {
    x := x + 1;
    while (p != null && p.x < 75)
      decreases 75 - p.x;
    {
      p.x := p.x + 1;
    }
  }

  method B(p: Modifies)
    modifies this;
  {
    call A(this);
    if (p == this) {
      call p.A(p);
    }
    call A(p);  // error: may violate modifies clause
  }

  method C(b: bool)
    modifies this;
    ensures !b ==> x == old(x) && next == old(next);
  {
  }

  method D(p: Modifies, y: int)
    requires p != null;
  {
    if (y == 3) {
      call p.C(true);  // error: may violate modifies clause
    } else {
      call p.C(false);  // error: may violation modifies clause (the check is done without regard
                        // for the postcondition, which also makes sense, since there may, in
                        // principle, be other fields of the object that are not constrained by the
                        // postcondition)
    }
  }

  method E()
    modifies this;
  {
    call A(null);  // allowed
  }

  method F(s: set<Modifies>)
    modifies s;
  {
    foreach (m in s | 2 <= m.x) {
      m.x := m.x + 1;
    }
    if (this in s) {
      x := 2 * x;
    }
  }

  method G(s: set<Modifies>)
    modifies this;
  {
    var m := 3;  // this is a different m

    foreach (m in s | m == this) {
      m.x := m.x + 1;
    }
    if (s <= {this}) {
      foreach (m in s) {
        m.x := m.x + 1;
      }
      call F(s);
    }
    foreach (m in s) {
      assert m.x < m.x + 10;  // nothing wrong with asserting something
      m.x := m.x + 1;  // error: may violate modifies clause
    }
  }
}

// ----------------- wellformed specifications ----------------------

class SoWellformed {
  var xyz: int;
  var next: SoWellformed;

  function F(x: int): int
  { 5 / x }  // error: possible division by zero

  function G(x: int): int
    requires 0 < x;
  { 5 / x }

  function H(x: int): int
    decreases 5/x;  // error: possible division by zero
  { 12 }

  function I(x: int): int
    requires 0 < x;
    decreases 5/x;
  { 12 }

  method M(a: SoWellformed, b: int) returns (c: bool, d: SoWellformed)
    requires a.xyz == 7;  // error: not always defined
    ensures c ==> d.xyz == -7;  // error: not always defined
    decreases 5 / b;  // error: not always defined
  {
    c := false;
  }

  method N(a: SoWellformed, b: int) returns (c: bool, d: SoWellformed)
    decreases 5 / b;
    requires a.next != null;  // error: not always defined
    requires a.next.xyz == 7;  // this is well-defined, given that the previous line is
    requires b < -2;
    ensures 0 <= b ==> d.xyz == -7 && !c;
  {
    c := true;
  }

  method O(a: SoWellformed, b: int) returns (c: bool, d: SoWellformed)
    modifies a.next;  // this may not be well-defined, but that's okay for modifies clauses
  {
    c := true;
  }

  method P(a: SoWellformed, b: int) returns (c: bool, d: SoWellformed);
    requires next != null;
    modifies this;
    ensures next.xyz < 100;  // error: may not be well-defined (if body sets next to null)

  method Q(a: SoWellformed, s: set<SoWellformed>) returns (c: bool, d: SoWellformed);
    requires next != null;
    modifies s;
    ensures next.xyz < 100;  // error: may not be well-defined (if this in s and body sets next to null)

  method R(a: SoWellformed, s: set<SoWellformed>) returns (c: bool, d: SoWellformed);
    requires next != null && this !in s;
    modifies s;
    ensures next.xyz < 100;  // fine
}
