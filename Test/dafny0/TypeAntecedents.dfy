// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// -------- This is an example of what was once logically (although not trigger-ly) unsound ---

datatype Wrapper<T> = Wrap(T)
datatype Unit = It
datatype Color = Yellow | Blue

function F(a: Wrapper<Unit>): bool
  ensures a == Wrapper.Wrap(Unit.It);
{
  match a
  case Wrap(u) => G(u)
}

function G(u: Unit): bool
  ensures u == Unit.It;
{
  match u
  case It => true
}

method BadLemma(c0: Color, c1: Color)
  ensures c0 == c1;
{
  var w0 := Wrapper.Wrap(c0);
  var w1 := Wrapper.Wrap(c1);

  // Manually, add the following assertions in Boogie.  (These would
  // b93e ill-typed in Dafny.)
  //     assert _default.F($Heap, this, w#06);
  //     assert _default.F($Heap, this, w#17);

  assert w0 == w1;  // this would be bad news (it should be reported as an error)
}

method Main() {
  BadLemma(Color.Yellow, Color.Blue);
  assert false;  // this shows how things can really go wrong if BadLemma verified successfully
}

// ---------------

class MyClass {
  var x: int;
  // The function axiom has "DType(this) == class.MyClass" in its antecedent.  Hence, it
  // is possible to prove the various asserts below only if the receiver is known by the
  // verifier to be of type MyClass.
  function H(): int { 5 }
}

datatype List =  Nil | Cons(MyClass?, List)

method M(list: List, S: set<MyClass>) returns (ret: int)
  modifies S;
  ensures ret == 7;
{  // error: postcondition violation (this postcondition tests that control does flow to the end)
  match (list) {
    case Nil =>
    case Cons(r,tail) =>
      if (r != null) {
        ghost var h := r.H();
        assert h == 5;
      } else {
        assert false;  // error
      }
  }
  var k := N();
  assert k.H() == 5;
  var st := new State;
  ghost var l := st.NF();
  assert l != null ==> l.H() == 5;

  forall s | s in S ensures true; { assert s.H() == 5; }
  forall s | s in S {
    s.x := 0;
  }

  assert (forall t: MyClass? :: t == null || t.H() == 5);
  // note, the definedness problem in the next line sits inside an unreachable branch
  assert (forall t: MyClass? :: t != null ==> (if t.H() == 5 then true else 10 / 0 == 3));

  assert TakesADatatype(List.Nil) == 12;
  assert TakesADatatype(List.Cons(null, List.Nil)) == 12;
  assert AlsoTakesADatatype(GenData.Pair(false, true)) == 17;
}

method N() returns (k: MyClass)
{
  k := new MyClass;
}

class State {
  var a: MyClass?
  function NF(): MyClass? reads this; { a }
}

function TakesADatatype(a: List): int { 12 }

datatype GenData<T> = Pair(T, T)

function AlsoTakesADatatype<U>(p: GenData<U>): int { 17 }
