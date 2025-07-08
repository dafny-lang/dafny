// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --general-traits=legacy "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module InterfaceHolder {
  trait {:termination false} Interface {
    method PutCacheEntry'()
  }
}

module InterfaceWrapper {
  import InterfaceHolder
  class InterfaceExtender extends InterfaceHolder.Interface {
    constructor () {
    }
    method PutCacheEntry'() {
    }
  }

  method PutCacheEntry(ex: InterfaceExtender) {
    ex.PutCacheEntry'();
  }
}

module TraitDefinitions {
  datatype Option<+T> = Some(value: T) | None {
    function Negate(t: T): Option<T> {
      match this {
        case Some(v) => None
        case None => Some(t)
      }
    }
    predicate IsFailure() {
      None?
    }
    function PropagateFailure<U>(): Option<U> {
      None
    }
    function Extract(): T
      requires !IsFailure() {
      value
    }
  }


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
    method GetD()  returns (d: int)

    function GetDFunc(): int
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
      this.z := 3;
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

    function GetDFunc(): int {
      d
    }
  }

  method Test(x: Option<int>) returns (r: Option<bool>) {
    r := Some(true);
  }

  method AcceptSubtraitIntInt(t: SubTrait<int, int>) {
  }

  datatype ObjectContainer = ObjectContainer(y: Y<int>)

  method ParameterBorrows(y: Y<int>, o: ObjectContainer) { // y is borrowed
    var z: SubTrait<int, int> := y as SubTrait<int, int>;
    var p: SuperTrait := y;
    var y2 := o.y; // y2 is owned
    ConsumeBorrows(y2 as SubTrait<int, int>);
    ConsumeBorrows(y2 as SubTrait<int, int>);
  }

  method ConsumeBorrows(y: SubTrait<int, int>) {

  }
  trait TraitNoArgs {}
  class ClassNoArgs extends TraitNoArgs {
    var x: int
    constructor() {
      x := 0;
    }
  }
  method ConsumeClassNoArgs(a: ClassNoArgs) {
  }

  method Main() {
    var rts := Test(Some(2));
    expect rts == Some(true);

    var y := new Y<int>(7);
    var yOwned := y;
    expect y.GetDFunc() == 2;
    AcceptSubtraitIntInt(yOwned);
    AcceptSubtraitIntInt(yOwned);
    var z: SubTrait<int, int> := yOwned as SubTrait<int, int>;
    var z2: SubTrait<int, int> := yOwned as SubTrait<int, int>;
    var w: SuperTrait := z;
    var w2: SuperTrait := z;
    var p: SuperTrait := y;
    /*var zy := z as Y<int>;
    var wy := w as Y<int>;
    var pzy := p as SubTrait<int, int> as Y<int>;
    expect zy == wy == pzy;*/
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
    expect y as object == p as object;
    expect yOwned as object == w as object;
    expect yOwned as object == p as object;
    var a := new ClassNoArgs();
    var aOwned := a;
    var o: TraitNoArgs := a as TraitNoArgs;
    expect o is ClassNoArgs;
    ConsumeClassNoArgs(o as ClassNoArgs);
    ConsumeClassNoArgs(o as ClassNoArgs);
    var oo: object := o as object;
    expect oo is ClassNoArgs;
    ConsumeClassNoArgs(oo as ClassNoArgs);
    ConsumeClassNoArgs(oo as ClassNoArgs);
    var objects := {y as object, w as object, p as object};
    expect |objects| == 1;
    var q := y as NoMemberTrait;
    expect y as NoMemberTrait == y;
    expect y as NoMemberTrait2 == y;
    expect y as NoMemberTrait as object == y as NoMemberTrait2;
    var yn := (q as object as Y<int>);
    expect yn.d == y.d;
    expect (q as object as Y<int>) == y;
    var yp: Y?<int> := null;
    expect yp == null;
    yp := y;
    expect yp == y;
    var ff := y.ClosureConvert();
    expect ff(1) == 1 + y.c + y.d;

    var seqY := [y];
    var setY := {y};
    var mulY := multiset{y};
    var mapY := map[1 := y];

    var seqYU: seq<SubTrait<int, int>> := seqY;
    var setYU: set<SubTrait<int, int>> := setY;
    var mulYU: multiset<SubTrait<int, int>> := mulY;
    var mapYU: map<int, SubTrait<int, int>> := mapY;

    var seqYS: seq<SuperTrait> := seqY;
    var setYS: set<SuperTrait> := setY;
    var mulYS: multiset<SuperTrait> := mulY;
    var mapYS: map<int, SuperTrait> := mapY;

    var seqYO: seq<object> := seqY;
    var seaYO: set<object> := setY;
    var mulYO: multiset<object> := mulY;
    var mapYO: map<int, object> := mapY;

    var seqYSO: seq<object> := seqYS;
    var seaYSO: set<object> := setYS;
    var mulYSO: multiset<object> := mulYS;
    var mapYSO: map<int, object> := mapYS;

    var optY := Some(y);
    var optYU: Option<SubTrait<int, int>> := optY;
    var optYS: Option<SuperTrait> := optY;
    var optYO: Option<object> := optY;
    var optYSO: Option<object> := optYS;

    print "Main passed all the tests\n";
  }
}
