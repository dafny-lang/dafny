// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  datatype Kind = Constant | Ident | Binary

  class Expr {
    var kind: Kind
    var value: int  // value if kind==Constant; id if kind==VarDecl; operator if kind==Binary
    var left: Expr?  // if kind==Binary
    var right: Expr?  // if kind==Binary

    ghost var Repr: set<object>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      Core() &&
      Valid'()
    }

    predicate Core()
      reads this, Repr
      decreases Repr, 0
    {
      this in Repr &&
      (left != null ==> left in Repr && this !in left.Repr && right !in left.Repr && left.Repr <= Repr && left.Valid()) &&
      (right != null ==> right in Repr && this !in right.Repr && left !in right.Repr && right.Repr <= Repr && right.Valid()) &&
      (kind == Binary ==> left != null && right != null && left.Repr !! right.Repr)
    }

    predicate Valid'()
      requires Core()
      reads this, Repr
      decreases Repr, 1

    constructor CreateConstant(x: int)
      ensures Valid() && fresh(Repr)
    {
      kind, value := Constant, x;
      left, right := null, null;
      Repr := {this};
      new;
      assume Valid'();  // to be proved in refinement modules
    }

    constructor CreateIdent(name: int)
      ensures Valid() && fresh(Repr)
    {
      kind, value := Ident, name;
      left, right := null, null;
      Repr := {this};
      new;
      assume Valid'();  // to be proved in refinement modules
    }

    constructor CreateBinary(op: int, left: Expr, right: Expr)
      requires left.Valid()
      requires right.Valid()
      requires left.Repr !! right.Repr
      ensures Valid() && fresh(Repr - left.Repr - right.Repr)
    {
      kind, value := Binary, op;
      this.left, this.right := left, right;
      Repr := {this} + left.Repr + right.Repr;
      new;
      assume Valid'();  // to be proved in refinement modules
    }
  }
}

// Introduce the idea of resolved
module M1 refines M0 {
  class Expr ... {
    ghost var resolved: bool

    predicate Valid'...
    {
      (resolved ==>
        (kind == Binary ==> left.resolved && right.resolved)) &&
      Valid''()
    }
    predicate Valid''()
      reads this, Repr
      ensures !resolved ==> Valid''()

    constructor CreateConstant...
    {
      resolved := false;
      new;
      assert ...;
    }

    constructor CreateIdent...
    {
      resolved := false;
      new;
      assert ...;
    }

    constructor CreateBinary...
    {
      resolved := false;
      new;
      assert ...;
    }

    method Resolve()
      requires Valid()  // it's okay if it's already resolved
      modifies Repr
      ensures Valid() && fresh(Repr - old(Repr))
      ensures resolved
      decreases Repr
    {
      if kind == Binary {
        left.Resolve();
        right.Resolve();
      }
      Repr := Repr + (if left != null then left.Repr else {}) + (if right != null then right.Repr else {});
      resolved := true;
      assume Valid'();  // to be checked in refinement modules
    }
  }
}

// Give "resolved" some meaning
module M2 refines M1 {
  class VarDecl {
  }

  class Expr ... {
    var decl: VarDecl?  // if kind==Ident, filled in during resolution

    predicate Valid''...
    {
      resolved ==>
        (kind == Ident ==> decl != null)
    }

    method Resolve...
    {
      if kind == Ident {
        decl := new VarDecl;
      }
      ...;
      assert ...;
    }
  }
}

// Finally, supposing each VarDecl has a value, evaluate a resolved expression
module M3 refines M2 {
  class VarDecl ... {
    var val: int
  }

  class Expr ... {
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
