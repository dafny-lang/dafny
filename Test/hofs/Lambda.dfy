// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method M<A>() {
    var f1 : A -> A := x   => x;
    var f2 : A -> A := (x) => x;
    var f3 : () -> () := () => ();
    var tt : () := ();
    var f4 : (A, A) -> (A, A) := (x, y) => (y, x);
    var f5 := (x : int) => x;

    var f6 := x requires x != 0 requires x != 1 => x;
    var f7 := x requires 0 != x requires x != 1 => x;
    assert f6(2) == f7(2);

    var u := 0;
    var f8 := () requires u == 0 => true;
    assert f8();
    u := 1;
    assert f8(); // ok, u value is copied at creation of f8

    var f9 := () requires u == 0 => true;
    assert !f9.requires();
}

datatype List<A> = Cons(A,List<A>) | Nil

method J(xs : List<int>) returns (z : int) {
    match xs
        case Cons(y,ys) => z := y;
        case Nil        => z := 0;

    if {
        case true => z := z;
        case true => z := 1;
    }
}

function Adder() : (int, int) -> int
  ensures forall x, y :: Adder().requires(x, y);
  ensures forall x, y :: (Adder())(x, y) == x + y;
{
  (x, y) => x + y
}

function MkId<A>() : A -> A
{
  x => x
}


// storage and references to functions
method T() {
   var f := x => x + 1;
   f := u => if u > 0 then f(u) else u;
   assert f(1) == 2 && f(0) == 0;
}

