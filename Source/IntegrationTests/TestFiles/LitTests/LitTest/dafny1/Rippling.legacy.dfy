// RUN: %dafny /compile:0 /deprecation:0 /induction:3 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Datatypes

datatype Bool = False | True

datatype Nat = Zero | Suc(Nat)

datatype List = Nil | Cons(Nat, List)

datatype Pair = Pair(Nat, Nat)

datatype PList = PNil | PCons(Pair, PList)

datatype Tree = Leaf | Node(Tree, Nat, Tree)

// Boolean functions

ghost function not(b: Bool): Bool
{
  match b
  case False => True
  case True => False
}

ghost function and(a: Bool, b: Bool): Bool
{
  if a == True && b == True then True else False
}

// Natural number functions

ghost function add(x: Nat, y: Nat): Nat
{
  match x
  case Zero => y
  case Suc(w) => Suc(add(w, y))
}

ghost function minus(x: Nat, y: Nat): Nat
{
  match x
  case Zero => Zero
  case Suc(a) => match y
    case Zero => x
    case Suc(b) => minus(a, b)
}

ghost function eq(x: Nat, y: Nat): Bool
{
  match x
  case Zero => (match y
    case Zero => True
    case Suc(b) => False)
  case Suc(a) => (match y
    case Zero => False
    case Suc(b) => eq(a, b))
}

ghost function leq(x: Nat, y: Nat): Bool
{
  match x
  case Zero => True
  case Suc(a) => match y
    case Zero => False
    case Suc(b) => leq(a, b)
}

ghost function less(x: Nat, y: Nat): Bool
{
  match y
  case Zero => False
  case Suc(b) => match x
    case Zero => True
    case Suc(a) => less(a, b)
}

ghost function min(x: Nat, y: Nat): Nat
{
  match x
  case Zero => Zero
  case Suc(a) => match y
    case Zero => Zero
    case Suc(b) => Suc(min(a, b))
}

ghost function max(x: Nat, y: Nat): Nat
{
  match x
  case Zero => y
  case Suc(a) => match y
    case Zero => x
    case Suc(b) => Suc(max(a, b))
}

// List functions

ghost function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x,tail) => Cons(x, concat(tail, ys))
}

ghost function mem(x: Nat, xs: List): Bool
{
  match xs
  case Nil => False
  case Cons(y, ys) => if x == y then True else mem(x, ys)
}

ghost function delete(n: Nat, xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) =>
    if y == n then delete(n, ys) else Cons(y, delete(n, ys))
}

ghost function drop(n: Nat, xs: List): List
{
  match n
  case Zero => xs
  case Suc(m) => match xs
    case Nil => Nil
    case Cons(x, tail) => drop(m, tail)
}

ghost function take(n: Nat, xs: List): List
{
  match n
  case Zero => Nil
  case Suc(m) => match xs
    case Nil => Nil
    case Cons(x, tail) => Cons(x, take(m, tail))
}

ghost function len(xs: List): Nat
{
  match xs
  case Nil => Zero
  case Cons(y, ys) => Suc(len(ys))
}

ghost function count(x: Nat, xs: List): Nat
{
  match xs
  case Nil => Zero
  case Cons(y, ys) =>
    if x == y then Suc(count(x, ys)) else count(x, ys)
}

ghost function last(xs: List): Nat
{
  match xs
  case Nil => Zero
  case Cons(y, ys) => match ys
    case Nil => y
    case Cons(z, zs) => last(ys)
}

ghost function apply(f: Nat -> Nat, xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) => Cons(f(y), apply(f, ys))
}

// In the following two functions, parameter "p" stands for a predicate:  applying p and
// getting Zero means "false" and getting anything else means "true".

ghost function takeWhileAlways(p: Nat -> Nat, xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) =>
    if p(y) != Zero
    then Cons(y, takeWhileAlways(p, ys))
    else Nil
}

ghost function dropWhileAlways(p: Nat -> Nat, xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) =>
    if p(y) != Zero
    then dropWhileAlways(p, ys)
    else Cons(y, ys)
}

ghost function filter(p: Nat -> Nat, xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) =>
    if p(y) != Zero
    then Cons(y, filter(p, ys))
    else filter(p, ys)
}

ghost function insort(n: Nat, xs: List): List
{
  match xs
  case Nil => Cons(n, Nil)
  case Cons(y, ys) =>
    if leq(n, y) == True
    then Cons(n, Cons(y, ys))
    else Cons(y, insort(n, ys))
}

ghost function ins(n: Nat, xs: List): List
{
  match xs
  case Nil => Cons(n, Nil)
  case Cons(y, ys) =>
    if less(n, y) == True
    then Cons(n, Cons(y, ys))
    else Cons(y, ins(n, ys))
}

ghost function ins1(n: Nat, xs: List): List
{
  match xs
  case Nil => Cons(n, Nil)
  case Cons(y, ys) =>
    if n == y
    then Cons(y, ys)
    else Cons(y, ins1(n, ys))
}

ghost function sort(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(y, ys) => insort(y, sort(ys))
}

ghost function reverse(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(t, rest) => concat(reverse(rest), Cons(t, Nil))
}

// Pair list functions

ghost function zip(a: List, b: List): PList
{
  match a
  case Nil => PNil
  case Cons(x, xs) => match b
    case Nil => PNil
    case Cons(y, ys) => PCons(Pair.Pair(x, y), zip(xs, ys))
}

ghost function zipConcat(x: Nat, xs: List, more: List): PList
{
  match more
  case Nil => PNil
  case Cons(y, ys) => PCons(Pair.Pair(x, y), zip(xs, ys))
}

// Binary tree functions

ghost function height(t: Tree): Nat
{
  match t
  case Leaf => Zero
  case Node(l, x, r) => Suc(max(height(l), height(r)))
}

ghost function mirror(t: Tree): Tree
{
  match t
  case Leaf => Leaf
  case Node(l, x, r) => Node(mirror(r), x, mirror(l))
}

// Function parameters

// The following functions stand for the constant "false" and "true" functions,
// respectively.

ghost function AlwaysFalseFunction(): Nat -> Nat { n => Zero }
ghost function AlwaysTrueFunction(): Nat -> Nat { n => Suc(Zero) }

lemma AboutAlwaysFalseFunction()
  ensures forall n :: AlwaysFalseFunction()(n) == Zero
{
}
lemma AboutAlwaysTrueFunction()
  ensures forall n :: AlwaysTrueFunction()(n) != Zero
{
}

// -----------------------------------------------------------------------------------
// The theorems to be proved
// -----------------------------------------------------------------------------------

lemma P1()
  ensures forall n, xs :: concat(take(n, xs), drop(n, xs)) == xs;
{
}

lemma P2()
  ensures forall n, xs, ys :: add(count(n, xs), count(n, ys)) == count(n, concat(xs, ys));
{
}

lemma P3()
  ensures forall n, xs, ys :: leq(count(n, xs), count(n, concat(xs, ys))) == True;
{
}

lemma P4()
  ensures forall n, xs :: add(Suc(Zero), count(n, xs)) == count(n, Cons(n, xs));
{
}

lemma P5()
  ensures forall n, xs, x ::
    add(Suc(Zero), count(n, xs)) == count(n, Cons(x, xs))
    ==> n == x;
{
  assert forall n :: Suc(n) > n;
}

lemma P6()
  ensures forall m, n :: minus(n, add(n, m)) == Zero;
{
}

lemma P7()
  ensures forall m, n :: minus(add(n, m), n) == m;
{
}

lemma P8()
  ensures forall k, m, n :: minus(add(k, m), add(k, n)) == minus(m, n);
{
}

lemma P9()
  ensures forall i, j, k :: minus(minus(i, j), k) == minus(i, add(j, k));
{
}

lemma P10()
  ensures forall m :: minus(m, m) == Zero;
{
}

lemma P11()
  ensures forall xs :: drop(Zero, xs) == xs;
{
}

lemma P12()
  ensures forall n, xs, f: Nat -> Nat :: drop(n, apply(f, xs)) == apply(f, drop(n, xs));
{
}

lemma P13()
  ensures forall n, x, xs :: drop(Suc(n), Cons(x, xs)) == drop(n, xs);
{
}

lemma P14()
  ensures forall xs, ys, p: Nat -> Nat :: filter(p, concat(xs, ys)) == concat(filter(p, xs), filter(p, ys));
{
}

lemma P15()
  ensures forall x, xs :: len(ins(x, xs)) == Suc(len(xs));
{
}

lemma P16()
  ensures forall x, xs :: xs == Nil ==> last(Cons(x, xs)) == x;
{
}

lemma P17()
  ensures forall n :: leq(n, Zero) == True <==> n == Zero;
{
}

lemma P18()
  ensures forall i, m :: less(i, Suc(add(i, m))) == True;
{
}

lemma P19()
  ensures forall n, xs :: len(drop(n, xs)) == minus(len(xs), n);
{
}

lemma P20()
  ensures forall xs :: len(sort(xs)) == len(xs);
{
  // the proof of this theorem requires a lemma about "insort"
  assert forall x, xs :: len(insort(x, xs)) == Suc(len(xs));
}

lemma P21()
  ensures forall n, m :: leq(n, add(n, m)) == True;
{
}

lemma P22()
  ensures forall a, b, c :: max(max(a, b), c) == max(a, max(b, c));
{
}

lemma P23()
  ensures forall a, b :: max(a, b) == max(b, a);
{
}

lemma P24()
  ensures forall a, b :: max(a, b) == a <==> leq(b, a) == True;
{
}

lemma P25()
  ensures forall a, b :: max(a, b) == b <==> leq(a, b) == True;
{
}

lemma P26()
  ensures forall x, xs, ys :: mem(x, xs) == True ==> mem(x, concat(xs, ys)) == True;
{
}

lemma P27()
  ensures forall x, xs, ys :: mem(x, ys) == True ==> mem(x, concat(xs, ys)) == True;
{
}

lemma P28()
  ensures forall x, xs :: mem(x, concat(xs, Cons(x, Nil))) == True;
{
}

lemma P29()
  ensures forall x, xs :: mem(x, ins1(x, xs)) == True;
{
}

lemma P30()
  ensures forall x, xs :: mem(x, ins(x, xs)) == True;
{
}

lemma P31()
  ensures forall a, b, c :: min(min(a, b), c) == min(a, min(b, c));
{
}

lemma P32()
  ensures forall a, b :: min(a, b) == min(b, a);
{
}

lemma P33()
  ensures forall a, b :: min(a, b) == a <==> leq(a, b) == True;
{
}

lemma P34()
  ensures forall a, b :: min(a, b) == b <==> leq(b, a) == True;
{
}

lemma P35()
  ensures forall xs :: dropWhileAlways(AlwaysFalseFunction(), xs) == xs;
{
}

lemma P36()
  ensures forall xs :: takeWhileAlways(AlwaysTrueFunction(), xs) == xs;
{
}

lemma P37()
  ensures forall x, xs :: not(mem(x, delete(x, xs))) == True;
{
}

lemma P38()
  ensures forall n, xs :: count(n, concat(xs, Cons(n, Nil))) == Suc(count(n, xs));
{
}

lemma P39()
  ensures forall n, x, xs ::
            add(count(n, Cons(x, Nil)), count(n, xs)) == count(n, Cons(x, xs));
{
}

lemma P40()
  ensures forall xs :: take(Zero, xs) == Nil;
{
}

lemma P41()
  ensures forall n, xs, f: Nat -> Nat :: take(n, apply(f, xs)) == apply(f, take(n, xs));
{
}

lemma P42()
  ensures forall n, x, xs :: take(Suc(n), Cons(x, xs)) == Cons(x, take(n, xs));
{
}

lemma P43(p: Nat -> Nat)
  ensures forall xs :: concat(takeWhileAlways(p, xs), dropWhileAlways(p, xs)) == xs;
{
}

lemma P44()
  ensures forall x, xs, ys :: zip(Cons(x, xs), ys) == zipConcat(x, xs, ys);
{
}

lemma P45()
  ensures forall x, xs, y, ys ::
            zip(Cons(x, xs), Cons(y, ys)) ==
            PCons(Pair.Pair(x, y), zip(xs, ys));
{
}

lemma P46()
  ensures forall ys :: zip(Nil, ys) == PNil;
{
}

lemma P47()
  ensures forall a :: height(mirror(a)) == height(a);
{
  // proving this theorem requires a previously proved lemma:
  P23();
}

// ...

lemma P54()
  ensures forall m, n :: minus(add(m, n), n) == m;
{
  // the proof of this theorem follows from two lemmas:
  assert forall m, n {:autotriggers false} :: minus(add(n, m), n) == m; // FIXME: Why does Autotriggers false make things verify?
  assert forall m, n :: add(m, n) == add(n, m);
}

lemma P65()
  ensures forall i, m :: less(i, Suc(add(m, i))) == True;
{
  if (*) {
    // the proof of this theorem follows from two lemmas:
    assert forall i, m {:autotriggers false} :: less(i, Suc(add(i, m))) == True; // FIXME: Why does Autotriggers false make things verify?
    assert forall m, n :: add(m, n) == add(n, m);
  } else {
    // a different way to prove it uses the following lemma:
    assert forall x,y :: add(x, Suc(y)) == Suc(add(x,y));
  }
}

lemma P67()
  ensures forall m, n :: leq(n, add(m, n)) == True;
{
  if (*) {
    // the proof of this theorem follows from two lemmas:
    assert forall m, n {:autotriggers false} :: leq(n, add(n, m)) == True; // FIXME: Why does Autotriggers false make things verify?
    assert forall m, n :: add(m, n) == add(n, m);
  } else {
    // a different way to prove it uses the following lemma:
    assert forall x,y :: add(x, Suc(y)) == Suc(add(x,y));
  }
}

// ---------
// Here is a alternate way of writing down the proof obligations:

lemma P1_alt(n: Nat, xs: List)
  ensures concat(take(n, xs), drop(n, xs)) == xs;
{
}

lemma P2_alt(n: Nat, xs: List, ys: List)
  ensures add(count(n, xs), count(n, ys)) == count(n, (concat(xs, ys)));
{
}

// ---------

lemma {:isolate_assertions} Lemma_RevConcat(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs));
{
  match (xs) {
    case Nil =>
      assert forall ws :: concat(ws, Nil) == ws;
    case Cons(t, rest) =>
      assert forall a, b, c :: concat(a, concat(b, c)) == concat(concat(a, b), c);
  }
}

lemma Theorem(xs: List)
  ensures reverse(reverse(xs)) == xs;
{
  match (xs) {
    case Nil =>
    case Cons(t, rest) =>
      Lemma_RevConcat(reverse(rest), Cons(t, Nil));
  }
}
