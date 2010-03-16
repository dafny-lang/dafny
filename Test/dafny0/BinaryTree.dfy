class IntSet {
  ghost var contents: set<int>;
  ghost var footprint: set<object>;

  var root: Node;

  function Valid(): bool
    reads this, footprint;
  {
    this in footprint &&
    (root == null ==> contents == {}) &&
    (root != null ==>
       root in footprint && root.footprint <= footprint && this !in root.footprint &&
       root.Valid() &&
       contents == root.contents)
  }

  method Init()
    modifies this;
    ensures Valid() && fresh(footprint - {this});
    ensures contents == {};
  {
    root := null;
    footprint := {this};
    contents := {};
  }

  method Find(x: int) returns (present: bool)
    requires Valid();
    ensures present <==> x in contents;
  {
    if (root == null) {
      present := false;
    } else {
      call present := root.Find(x);
    }
  }

  method Insert(x: int)
    requires Valid();
    modifies footprint;
    ensures Valid() && fresh(footprint - old(footprint));
    ensures contents == old(contents) + {x};
  { 
    call t := InsertHelper(x, root);
    root := t;
    contents := root.contents;
    footprint := root.footprint + {this};
  }

  static method InsertHelper(x: int, n: Node) returns (m: Node)
    requires n == null || n.Valid();
    modifies n.footprint;
    ensures m != null && m.Valid();
    ensures n == null ==> fresh(m.footprint) && m.contents == {x};
    ensures n != null ==> m == n && n.contents == old(n.contents) + {x};
    ensures n != null ==> fresh(n.footprint - old(n.footprint));
    decreases if n == null then {} else n.footprint;
  {
    if (n == null) {
      m := new Node;
      call m.Init(x);
    } else if (x == n.data) {
      m := n;
    } else {
      if (x < n.data) {
        call t := InsertHelper(x, n.left);
        n.left := t;
        n.footprint := n.footprint + n.left.footprint;
      } else {
        call t := InsertHelper(x, n.right);
        n.right := t;
        n.footprint := n.footprint + n.right.footprint;
      }
      n.contents := n.contents + {x};
      m := n;
    }
  }

  method Remove(x: int)
    requires Valid();
    modifies footprint;
    ensures Valid() && fresh(footprint - old(footprint));
    ensures contents == old(contents) - {x};
  {
    if (root != null) {
      call newRoot := root.Remove(x);
      root := newRoot;
      if (root == null) {
        contents := {};
        footprint := {this};
      } else {
        contents := root.contents;
        footprint := root.footprint + {this};
      }
    }
  }
}

class Node {
  ghost var contents: set<int>;
  ghost var footprint: set<object>;

  var data: int;
  var left: Node;
  var right: Node;

  function Valid(): bool
    reads this, footprint;
  {
    this in footprint &&
    null !in footprint &&
    (left != null ==>
      left in footprint &&
      left.footprint <= footprint && this !in left.footprint &&
      left.Valid() &&
      (forall y :: y in left.contents ==> y < data)) &&
    (right != null ==>
      right in footprint &&
      right.footprint <= footprint && this !in right.footprint &&
      right.Valid() &&
      (forall y :: y in right.contents ==> data < y)) &&
    (left == null && right == null ==>
      contents == {data}) &&
    (left != null && right == null ==>
      contents == left.contents + {data}) &&
    (left == null && right != null ==>
      contents == {data} + right.contents) &&
    (left != null && right != null ==>
      left.footprint !! right.footprint &&
      contents == left.contents + {data} + right.contents)
  }

  method Init(x: int)
    modifies this;
    ensures Valid() && fresh(footprint - {this});
    ensures contents == {x};
  {
    data := x;
    left := null;
    right := null;
    contents := {x};
    footprint := {this};
  }

  method Find(x: int) returns (present: bool)
    requires Valid();
    ensures present <==> x in contents;
    decreases footprint;
  {
    if (x == data) {
      present := true;
    } else if (left != null && x < data) {
      call present := left.Find(x);
    } else if (right != null && data < x) {
      call present := right.Find(x);
    } else {
      present := false;
    }
  }

  method Remove(x: int) returns (node: Node)
    requires Valid();
    modifies footprint;
    ensures fresh(footprint - old(footprint));
    ensures node != null ==> node.Valid();
    ensures node == null ==> old(contents) <= {x};
    ensures node != null ==> node.footprint <= footprint && node.contents == old(contents) - {x};
    decreases footprint;
  {
    node := this;
    if (left != null && x < data) {
      call t := left.Remove(x);
      left := t;
      contents := contents - {x};
      if (left != null) { footprint := footprint + left.footprint; }
    } else if (right != null && data < x) {
      call t := right.Remove(x);
      right := t;
      contents := contents - {x};
      if (right != null) { footprint := footprint + right.footprint; }
    } else if (x == data) {
      if (left == null && right == null) {
        node := null;
      } else if (left == null) {
        node := right;
      } else if (right == null) {
        node := left;
      } else {
        // rotate
        call min, r := right.RemoveMin();
        data := min;  right := r;
        contents := contents - {x};
        if (right != null) { footprint := footprint + right.footprint; }
      }
    }
  }

  method RemoveMin() returns (min: int, node: Node)
    requires Valid();
    modifies footprint;
    ensures fresh(footprint - old(footprint));
    ensures node != null ==> node.Valid();
    ensures node == null ==> old(contents) == {min};
    ensures node != null ==> node.footprint <= footprint && node.contents == old(contents) - {min};
    ensures min in old(contents) && (forall x :: x in old(contents) ==> min <= x);
    decreases footprint;
  {
    if (left == null) {
      min := data;
      node := right;
    } else {
      call min, t := left.RemoveMin();
      left := t;
      node := this;
      contents := contents - {min};
      if (left != null) { footprint := footprint + left.footprint; }
    }
  }
}

class Main {
  method Client0(x: int)
  {
    var s := new IntSet;
    call s.Init();

    call s.Insert(12);
    call s.Insert(24);
    call present := s.Find(x);
    assert present <==> x == 12 || x == 24;
  }

  method Client1(s: IntSet, x: int)
    requires s != null && s.Valid();
    modifies s.footprint;
  {
    call s.Insert(x);
    call s.Insert(24);
    assert old(s.contents) - {x,24} == s.contents - {x,24};
  }
}
