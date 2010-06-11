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
    requires if next == null then 5/x < 20 else true;  // error: ill-defined then branch
    requires if next == null then true else 0 <= 5/x;  // error: ill-defined then branch
    requires if next.next == null then true else true;  // error: ill-defined guard
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
      decreases 75 - p.x;  // error: not defined at top of each iteration (there's good reason to
    {                      // insist on this; for example, the decrement check could not be performed
      p.x := p.x + 1;      // at the end of the loop body if p were set to null in the loop body)
    }
  }

  method Aprime(p: Modifies)
    modifies this, p;
  {
    x := x + 1;
    while (p != null && p.x < 75)
      decreases if p != null then 75 - p.x else 0;  // given explicitly (but see Adoubleprime below)
    {
      p.x := p.x + 1;
    }
  }

  method Adoubleprime(p: Modifies)
    modifies this, p;
  {
    x := x + 1;
    while (p != null && p.x < 75)  // here, the decreases clause is heuristically inferred (to be the
    {                              // same as the one in Aprime above)
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

  method SetConstruction() {
    var s := {1};
    assert s != {};
    if (*) {
      assert s != {0,1};
    } else {
      assert s != {1,0};
    }
  }
}
