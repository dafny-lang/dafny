module TraitDefinitions {
  trait NoMemberTrait {}
  
  trait NoMemberTrait2 {}
  trait SuperTrait extends NoMemberTrait, NoMemberTrait2 {
    method GetC() returns (c: int)
    method SetC(newC: int)
      modifies this
  }

  trait {:termination false} SubTrait<T, I> extends SuperTrait {
    method GetC() returns (c: int)
      ensures c >= 0

    method GetCTwicePlusD() returns (c2: int) {
      var c := GetC();
      var d := GetD();
      return c + c + d;
    }
    method GetD() returns (d: int)
  }
}

module All {
  import opened TraitDefinitions
  
  class Y<I> extends SubTrait<int, I> {
    var c: int
    var z: int
    const d: int := 2
    constructor(c: int) {
      this.c := c;
    }
    method AddZ()
      modifies this
    {
      this.Add(this.z);
    }
    method Add(extra: int)
      modifies this
    {
      c := c + extra;
    }
    method Swap()
      modifies this
    {
      this.c, this.z := this.z, this.c;
    }
    method SetC(newC: int)
      modifies this
    {
      c := newC;
    }
    method GetC() returns (c: int)
      ensures c >= 0
    {
      return if this.c <= 0 then 37 else this.c;
    }
    method GetD() returns (d: int) {
      return this.d;
    }
    method Convert(i: I, i2: I) returns (j: I) {
      if c == 0 {
        return i;
      } else {
        return i2;
      }
    }
    method ClosureConvert() returns (f: int ~> int)
      ensures forall i :: f.requires(i) == true && f.reads(i) == {this}
    {
      return (i: int) reads this => this.c + this.d + i;
    }
  }

  method Main() {
    var y := new Y<int>(7);
    var z: SubTrait<int, int> := y as SubTrait<int, int>;
    var w: SuperTrait := z;
    var p: SuperTrait := y;
    var zc := z.GetC();
    var wc := w.GetC();
    var pc := p.GetC();
    expect 7 == y.c == zc == wc == pc;
    var zd := z.GetD();
    var yd := y.GetD();
    expect yd == zd == 2;
    var zc2d := z.GetCTwicePlusD();
    expect zc2d == 16;
    var yc2d := y.GetCTwicePlusD();
    expect yc2d == 16;
    var f := y.Convert(42, 37);
    expect f == 37;
    w.SetC(0);
    f := y.Convert(42, 37);
    expect f == 42;
    expect y as object == w as object;
    var objects := {y as object, w as object, p as object};
    expect |objects| == 1;
    var q := y as NoMemberTrait;
    expect y as NoMemberTrait == y;
    expect y as NoMemberTrait2 == y;
    expect y as NoMemberTrait as object == y as NoMemberTrait2;
    var yp: Y?<int> := null;
    expect yp == null;
    yp := y;
    expect yp == y;
    var ff := y.ClosureConvert();
    expect ff(1) == 1 + y.c + y.d;
  }
}