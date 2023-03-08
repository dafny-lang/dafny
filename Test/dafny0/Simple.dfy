// RUN: %dafny /dprint:- /env:0 /noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// My first Dafny program
// Rustan Leino, 27 January 2008

class MyClass<T,U> {
  var x: int;

  method M(s: bool, lotsaObjects: set<object>) returns (t: object, u: set<int>, v: seq<MyClass?<bool,U>>)
    requires s;
    modifies this, lotsaObjects;
    ensures t == t;
    ensures old(null) != this; // warning: old(null) is the same as null
  {
    x := 12;
    while (x < 100)
      invariant x <= 100;
    {
      x := x + 17;
      if (x % 20 == 3) {
        x := this.x + 1;
      } else {
        this.x := x + 0;
      }
      t, u, v := M(true, lotsaObjects);
      var to: MyClass<T,U>;
      t, u, v := this.M(true, lotsaObjects);
      t, u, v := to.M(true, lotsaObjects);
      assert v[x] != null ==> null !in v[2..x][1..][5 := v[this.x]][..10];
    }
  }

  ghost function F(x: int, y: int, h: WildData, k: WildData): WildData
  {
    if x < 0 then h else
    if (x == 0) then
      if if h==k then true else false then h else if y == 0 then k else h
    else k
  }
}

// some datatype stuff:

datatype List<T> = Nil | Cons(T, List<T>)

datatype WildData =
  Something() |
  JustAboutAnything(bool, myName: set<int>, int, WildData) |
  More(List<int>)

class C {
  var w: WildData;
  var list: List<bool>;
}

lemma M(x: int)
  ensures x < 8;
{
  // proof would go here
}
greatest lemma M'(x': int)
  ensures true;
{
}

// modifiers on functions

class CF {
  static ghost function F(): int
  predicate G()
  greatest predicate Co()
  ghost function H(): int
  static ghost function I(): real
  static ghost predicate J()
}

// test printing of various if statements, including with omitted guards
module A {
  method P(x: int, y: int) {
    if x==2 {
    } else if * {
    }
    if x==10 {
    }
    if y==0 {
    } else if y==1 {
    } else if * {
    } else if y==2 {
    } else if (*) {
    } else if y == 3 {
    } else {
    }
  }
}
module B refines A {
  method P... {
    if ... {
    } else if x==3 {
    }
    ...;
  }
}
