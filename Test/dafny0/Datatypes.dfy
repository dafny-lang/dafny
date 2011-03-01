datatype List<T> {
  Nil;
  Cons(T, List<T>);
}

class Node {
  var data: int;
  var next: Node;

  function Repr(list: List<int>): bool
    reads *;
    decreases list;
  { match list
    case Nil =>
      next == null
    case Cons(d,cdr) =>
      data == d && next != null && next.Repr(cdr)
  }

  method Init()
    modifies this;
    ensures Repr(#List.Nil);
  {
    next := null;
  }

  method Add(d: int, L: List<int>) returns (r: Node)
    requires Repr(L);
    ensures r != null && r.Repr(#List.Cons(d, L));
  {
    r := new Node;
    r.data := d;
    r.next := this;
  }
}

class AnotherNode {
  var data: int;
  var next: AnotherNode;

  function Repr(n: AnotherNode, list: List<int>): bool
    reads *;
    decreases list;
  { match list
    case Nil =>
      n == null
    case Cons(d,cdr) =>
      n != null && n.data == d && Repr(n.next, cdr)
  }

  method Create() returns (n: AnotherNode)
    ensures Repr(n, #List.Nil);
  {
    n := null;
  }

  method Add(n: AnotherNode, d: int, L: List<int>) returns (r: AnotherNode)
    requires Repr(n, L);
    ensures Repr(r, #List.Cons(d, L));
  {
    r := new AnotherNode;
    r.data := d;
    r.next := n;
  }
}

method TestAllocatednessAxioms(a: List<Node>, b: List<Node>, c: List<AnotherNode>)
{
  var n := new Node;
  var p := n;
  match a {
    case Nil =>
    case Cons(x, tail) => assert x != n; p := x;
  }
  match b {
    case Nil =>
    case Cons(x, tail) =>
      match tail {
        case Nil =>
        case Cons(y, more) =>
          assert y != n;
          assert y != p;  // error: if p is car(a), then it and y may very well be equal
      }
  }
  match c {
    case Nil =>
    case Cons(x, tail) =>
      match tail {
        case Nil =>
        case Cons(y, more) =>
          var o: object := y;
          assert p != null ==> p != o;  // follows from well-typedness
      }
  }
}

class NestedMatchExpr {
  function Cadr<T>(a: List<T>, default: T): T
  {
    match a
    case Nil => default
    case Cons(x,t) =>
      match t
      case Nil => default
      case Cons(y,tail) => y
  }
  // CadrAlt is the same as Cadr, but it writes its two outer cases in the opposite order
  function CadrAlt<T>(a: List<T>, default: T): T
  {
    match a
    case Cons(x,t) => (
      match t
      case Nil => default
      case Cons(y,tail) => y)
    case Nil => default
  }
  method TestNesting0()
  {
    var x := 5;
    var list := #List.Cons(3, #List.Cons(6, #List.Nil));
    assert Cadr(list, x) == 6;
    match (list) {
      case Nil => assert false;
      case Cons(h,t) => assert Cadr(t, x) == 5;
    }
  }
  method TestNesting1(a: List<NestedMatchExpr>)
    ensures Cadr(a, this) == CadrAlt(a, this);
  {
    match (a) {
      case Nil =>
      case Cons(x,t) =>
        match (t) {
          case Nil =>
          case Cons(y,tail) =>
        }
    }
  }
}
