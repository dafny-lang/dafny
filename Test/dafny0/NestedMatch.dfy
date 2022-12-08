// RUN: %exits-with 4 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NestedMatch {
  datatype Nat = Zero | Suc(Nat)

  predicate Even(n: Nat)
  {
    match n
    case Zero => true
    case Suc(Zero) => false
    case Suc(Suc(p)) => Even(p)
  }


  method checkEven(n: Nat) {
    assert Even(Zero) == true;
    assert Even(Suc(Zero)) == false;
    assert Even(Suc(Suc(n))) == Even(n);
  }

  datatype List<T> = Nil | Cons(T, List<T>)

  function last<T>(xs: List<T>): T
    requires xs != Nil
  {
    match xs
    case Cons(y, Nil) => y
    case Cons(y, Cons(z, zs)) => last(Cons(z, zs))
  }

  method checkLast<T>(y: T) {
    assert last(Cons(y, Nil)) == y;
    assert last(Cons(y, Cons(y, Nil))) == last(Cons(y, Nil));
  }


  function minus(x: Nat, y: Nat): Nat
  {
    match (x, y)
    case (Zero, _) => Zero
    case (Suc(_), Zero) => x
    case (Suc(a), Suc(b)) => minus(a, b)
  }

  method checkMinus(x:Nat, y: Nat) {
    assert minus(Suc(x), Suc(y)) == minus(x,y);
  }


  // nested match statement
  method Last<T>(xs: List<T>) returns (x: T)
    requires xs != Nil
  {

    match xs {
	  case Cons(y, Nil) => x:= y;
	  case Cons(y, Cons(z, zs)) => x:=Last(Cons(z, zs));
    }
  }
}

module MatchInCalc_Module {  // regression tests
  datatype T = Leaf(h: int) | Node(g: int)
  predicate P(t: T)
  predicate Q(t: T)
  function F(t: T): int {
    match t
    case Leaf(r0) => r0
    case Node(r1) => 2 * r1
  }

  lemma MatchInCalc(t: T)
    requires !P(t) && Q(t) && t.Node?
  {
    calc {
      P(t);
    ==
      match t
      case Leaf(v) => 2 == 10 / v
      case Node(x) => false;
    ==
      !Q(t);
    }
  }
  lemma LetInCalc(t: T, e: int)
    requires P(t) && Q(t) && e == 5
  {
    calc {
      P(t);
    ==
      var y := e; 2 == 10 / y;
    ==
      Q(t);
    }
  }
  lemma MissingCase(t: T)
    requires !P(t) && !Q(t) && t == Leaf(1)
  {
    calc {
      P(t);
    ==
      match t
      case Leaf(w) => 2 == 10 / w;
    ==
      Q(t);
    }
  }
  lemma FunctionX(t: T)
  {
    calc {
      F(t);
    ==
      match t
      case Leaf(s0) => s0
      case Node(s1) => 2 * s1;
    ==
      if t.Leaf? then t.h else t.g + t.g;
    }
  }
  lemma FunctionY(t: T)
  {
    calc {
      F(t) == 11;
    ==
      (match t
      case Leaf(s0) => s0
      case Node(s1) => 2 * s1) == 11;
    ==
      match t
      case Leaf(s0) => s0 == 11
      case Node(s1) => 2 * s1 == 11;
    ==  // 11 is not even
      t == Leaf(11);
    }
  }
  lemma FunctionZ(t: T, tx: T, ty: T)
  {
    calc {
      F(if F(t) == 13 then tx else ty) == 11;
    ==
      (match if F(t) == 13 then tx else ty
      case Leaf(s0) => s0
      case Node(s1) => 2 * s1) == 11;
    ==
      match if F(t) == 13 then tx else ty
      case Leaf(s0) => s0 == 11
      case Node(s1) => 2 * s1 == 11;
    ==
      match
        if
	  match t {
          case Leaf(s0) => s0
          case Node(s1) => 2 * s1}
        == 13 then tx else ty
      case Leaf(s0) => s0 == 11
      case Node(s1) => 2 * s1 == 11;
    ==
      match
        if
	  match t {
          case Leaf(e0) => e0
          case Node(e1) => 2 * e1}
        == 13 then tx else ty
      case Leaf(s0) => s0 == 11
      case Node(s1) => 2 * s1 == 11;
    <==
      t.Node? &&
      match ty
      case Leaf(s0) => s0 == 11
      case Node(s1) => 2 * s1 == 11;
    ==
      t.Node? && ty == Node(22);  // error (actually, ty == Leaf(11))
    }
  }
}
