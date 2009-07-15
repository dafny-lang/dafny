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
    var kz;
    call kz := M(t,u);
    assert kz && (G() || !G());
  }

  function G<Y>(): Y;
}
