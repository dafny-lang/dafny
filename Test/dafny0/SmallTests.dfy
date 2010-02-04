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
