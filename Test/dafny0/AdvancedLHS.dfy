/*
---
compile: 0 
allocated: [1, 3] 
*/
class C {
  var x: C?

  method M(S: set<C>, a: array<C>, b: array2<C>)
    requires S != {}
    modifies this, a, b
  {
    x := new C;
    x := new C.Init();
    x := *;

    // test evaluation order
    var c := x;
    x := null;
    x := new C.InitOther(x);  // since the parameter is evaluated before the LHS is set, the precondition is met
    assert x != c;

    // test evaluation order and modification
    if (*) {
      var k := this.x;
      var kx := this.x.x;
      this.x.x := new C.InitAndMutate(this);
      assert this.x == null;
      assert this.x != k;
      assert k.x != kx;  // because it was set to a new object
      assert fresh(k.x);
    } else {
      var k := this.x;
      var kx := this.x.x;
      this.x.x := new C.InitAndMutate(this);
      var t := this.x.x;  // error: null dereference (because InitAndMutate set this.x to null)
    }

    if 10 <= a.Length {
      a[2] := new C;
      a[3] := *;
    }
    if 10 <= b.Length0 && 20 <= b.Length1 {
      b[2,14] := new C;
      b[3,11] := *;
    }
  }

  method Init() { }
  method InitOther(c: C?)
    requires c == null
  {
    var d := new int[if c == null then 10 else -3];  // run-time error if c were non-null, but it ain't
  }
  method InitAndMutate(c: C)
    modifies c
    ensures c.x == null
  {
    c.x := null;
  }
}
