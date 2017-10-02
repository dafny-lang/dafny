// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  datatype Kind = Constant | Ident | Binary

  class Expr {
    var kind: Kind
    var value: int  // value if kind==Constant; id if kind==VarDecl; operator if kind==Binary
    var left: Expr?  // if kind==Binary
    var right: Expr?  // if kind==Binary

    ghost var Repr: set<object>

    protected predicate Valid()
      reads this, Repr
    {
      this in Repr &&
      (left != null ==> left in Repr && this !in left.Repr && right !in left.Repr && left.Repr <= Repr && left.Valid()) &&
      (right != null ==> right in Repr && this !in right.Repr && left !in right.Repr && right.Repr <= Repr && right.Valid()) &&
      (kind == Binary ==> left != null && right != null && left.Repr !! right.Repr)
    }

    constructor CreateConstant(x: int)
      ensures Valid() && fresh(Repr - {this})
    {
      kind, value := Constant, x;
      left, right := null, null;
      Repr := {this};
    }

    constructor CreateIdent(name: int)
      ensures Valid() && fresh(Repr - {this})
    {
      kind, value := Ident, name;
      left, right := null, null;
      Repr := {this};
    }

    constructor CreateBinary(op: int, left: Expr, right: Expr)
      requires left.Valid()
      requires right.Valid()
      requires left.Repr !! right.Repr
      ensures Valid() && fresh(Repr - {this} - left.Repr - right.Repr)
    {
      kind, value := Binary, op;
      this.left, this.right := left, right;
      Repr := {this} + left.Repr + right.Repr;
    }
  }
}

// Introduce the idea of resolved
module M1 refines M0 {
  class Expr {
    ghost var resolved: bool

    protected predicate Valid()
    {
      resolved ==>
        (kind == Binary ==> left.resolved && right.resolved)
    }

    constructor CreateConstant...
    {
      resolved := false;
    }

    constructor CreateIdent...
    {
      resolved := false;
    }

    constructor CreateBinary...
    {
      resolved := false;
    }

    method Resolve()
      requires Valid()  // it's okay if it's already resolved
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures resolved
      decreases Repr
    {
      if (kind == Binary) {
        left.Resolve();
        right.Resolve();
      }
      Repr := Repr + (if left != null then left.Repr else {}) + (if right != null then right.Repr else {});
      resolved := true;
    }
  }
}

// Give "resolved" some meaning
module M2 refines M1 {
  class VarDecl {
  }

  class Expr {
    var decl: VarDecl?  // if kind==Ident, filled in during resolution

    protected predicate Valid()
    {
      resolved ==>
        (kind == Ident ==> decl != null)
    }

    method Resolve...
    {
      if (kind == Ident) {
        decl := new VarDecl;
      }
    }
  }
}

// Finally, supposing each VarDecl has a value, evaluate a resolved expression
module M3 refines M2 {
  class VarDecl {
    var val: int
  }

  class Expr {
    method Eval() returns (r: int)
      requires Valid()
      requires resolved
      decreases Repr
    {
      match (kind) {
        case Constant =>
          r := value;
        case Ident =>
          r := decl.val;  // note how this statement relies on "decl" being non-null, which follows from the expression being resolved
        case Binary =>
          var x := left.Eval();
          var y := right.Eval();
          r := x + y;
      }
    }
  }
}
