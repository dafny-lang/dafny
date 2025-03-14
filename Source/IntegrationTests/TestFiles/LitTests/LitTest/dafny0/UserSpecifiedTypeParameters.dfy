// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  class MyClass<T(==),U(==)> {
    var s: map<T,set<U>>
    static ghost function F<W>(w: W, w': W, t: T, u: U): int
    {
      if w == w' then 5 else 7
    }
    ghost function G<Y>(y: Y): Y { y }
    static ghost function H<Y>(y: Y): (T, U, Y)

    ghost method M() {
      var f0 := F<int>;
      var f1 := MyClass<int,bool>.F<real>;
      var g0 := G;
      var x := g0(500);
      var g1 := G<real>;

      var mc: MyClass<int,bool>, tt, uu, yy;
      var h0 := mc.H(5.0);
      tt, uu, yy := h0.0, h0.1, h0.2;
      if (tt, uu, yy) == MyClass.H(4.0) {
      }
      var h1 := MyClass.H(4.0);  // error: types to MyClass underspecified
      var h2 := MyClass<bool, int>.H(4.0);
      var pt: T, pu: U;
      var h3 := MyClass<T,U>.H(3.2);
      h3 := MyClass.H(3.2);
      pt := h3.0;
      pu := h3.1;
      var r := h3.2 + 0.3;
    }
  }
}

module M1 {
  class C0 {
    function F(x: bool, y: bool): () { () }
    method M0(a: int, b: int, c: int, d: int) {
      var u := F( a < b , (c > (d)) );
      var v := F( a < b , c > d );
    }
    method M1(a: int, b: int, c: int, d: int) {
      var u := F( a < b , c > (d) );  // error: undefined types b,c; undefined function a; wrong # args to F
    }
  }
  class C1 {
    function F(x: int): () { () }
    function a<T,U>(x: int): int { x }
    method M<b, c>(d: int) {
      var u;
      u := F( a < b , c > (d) );
    }
    method P<g,h,m,n>() {
      assert a<g,h> == a<m,n>;
    }
  }
}

module M2 {
  class ClassA {
    ghost function F<A>(a: A): int

    lemma Lem<Y>() returns (y: Y)

    lemma M<X>(x: X)
    {
      var k := Lem<int>();
    }
  }
  class ClassB {
    lemma LemmaX<A>(y: A)
    lemma LemmaY<A>(x: int)
    {
      LemmaX<A>(x);  // error: The given type instantiation A does not agree with the type of parameter x
    }

    lemma LemmaR<T>(x: int)
    lemma LemmaS<A>()
    {
      LemmaR<A>(5);
    }

    ghost function FuncX<A>(y: A): real
    ghost function FuncY<A>(x: int): real
    {
      FuncX<A>(x)  // error: The given type instantiation A does not agree with the type of parameter x
    }

    ghost function FuncR<T>(x: int): real
    ghost function FuncS<A>(): real
    {
      FuncR<A>(5)
    }
  }
}
