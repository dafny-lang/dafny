// My first Dafny program
// Rustan Leino, 27 January 2008

class MyClass<T,U> {
  var x: int;

  method M(s: bool, lotsaObjects: set<object>) returns (t: object, u: set<int>, v: seq<MyClass<bool,U>>)
    requires s;
    modifies this, lotsaObjects;
    ensures t == t;
    ensures old(null) != this;
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
      call t, u, v := M(true, lotsaObjects);
      var to: MyClass<T,U>;
      call to, u, v := this.M(true, lotsaObjects);
      call to, u, v := to.M(true, lotsaObjects);
    }
  }
}
