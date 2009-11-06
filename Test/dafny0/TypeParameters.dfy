class C<U> {
  method M<T>(x: T, u: U) returns (y: T)
    ensures x == y && u == u;
  {
    y := x;
  }

  function F<X>(x: X, u: U): bool
  {
    x == x && u == u
  }

  method Main(u: U)
  {
    var t := F(3,u) && F(this,u);
    call kz := M(t,u);
    assert kz && (G() || !G());
  }

  function G<Y>(): Y;
}

class SetTest {
  method Add<T>(s: set<T>, x: T) returns (t: set<T>)
    ensures t == s + {x};
  {
    t := s + {x};
  }

  method Good()
  {
    var s := {2, 5, 3};
    call t := Add(s, 7);
    assert {5,7,2,3} == t;
  }

  method Bad()
  {
    var s := {2, 50, 3};
    call t := Add(s, 7);
    assert {5,7,2,3} == t;  // error
  }
}

class SequenceTest {
  method Add<T>(s: seq<T>, x: T) returns (t: seq<T>)
    ensures t == s + [x];
  {
    t := s + [x];
  }

  method Good()
  {
    var s := [2, 5, 3];
    call t := Add(s, 7);
    assert [2,5,3,7] == t;
  }

  method Bad()
  {
    var s := [2, 5, 3];
    call t := Add(s, 7);
    assert [2,5,7,3] == t || [2,5,3] == t;
  }
}
