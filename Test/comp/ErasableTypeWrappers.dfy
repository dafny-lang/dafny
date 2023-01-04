// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype SingletonRecord = SingletonRecord(u: int)
datatype GhostOrNot = ghost Ghost(a: int, b: int) | Compiled(x: int)
datatype GenericGhostOrNot<X> = ghost Ghost(a: int, b: int) | GenericCompiled(x: X)
datatype GenericSingletonPlusGhost<X> = GenericSingletonPlusGhost(ghost decade: int, x: X)

method Main() {
  TestTargetTypesAndConstructors();
  TestSelect();
  TestUpdate();
  TestDiscriminators();
  TestMatchStmt();
  TestMatchExpr();
  TestEquality();
  TestDefaultValues<SingletonRecord, SingleOdd>();
  TestTypeParameters(GenericCompiled("<gen>"), GenericCompiled(3.14), GenericCompiled(2.7));
  TestMembers();
  OptimizationChecks.Test();
}

method TestTargetTypesAndConstructors() {
  var r := SingletonRecord(62); // type of r should turn into int
  var g := Compiled(63); // type of g should turn into int
  var rst := (2, 5);
  var xyz := (2, ghost 3, 5); // type of xyz should turn into Tuple2
  var abc := (ghost 2, 3, ghost 5); // type of abc should turn into int
  var gen := GenericCompiled("<gen>");

  print r, " ", g, " ", rst, " ", xyz, " ", abc, " ", gen, "\n"; // 62 63 (2, 5) (2, 5) 3 <gen>
}

method TestSelect() {
  var r := SingletonRecord(62);
  var g := Compiled(63);
  var rst := (2, 5);
  var xyz := (2, ghost 3, 5);
  var abc := (ghost 2, 3, ghost 5);
  var gen := GenericSingletonPlusGhost(1980, "<gen>");

  print r.u, " "; // 62
  print g.x, " "; // 63
  print rst.1, " "; // 5
  print xyz.2, " "; // 5
  print abc.1, " "; // 3
  print gen.x, "\n"; // <gen>
}

method TestUpdate() {
  var r := SingletonRecord(62);
  var g := Compiled(63);
  var rst := (2, 5);
  var xyz := (2, ghost 3, 5);
  var abc := (ghost 2, 3, ghost 5);
  var gen := GenericSingletonPlusGhost(1980, "<gen>");

  rst := rst.(0 := 888);
  xyz := xyz.(0 := 888);
  abc := abc.(0 := 888); // no-op
  gen := gen.(decade := 1982); // no-op

  print rst.1, " "; // 5
  print xyz.2, " "; // 5
  print abc.1, " "; // 3
  print gen.x, "\n"; // <gen>

  r := r.(u := 1062); // rhs optimized to just 1062
  g := g.(x := 1063); // rhs optimized to just 1063
  rst := rst.(1 := 1005);
  xyz := xyz.(2 := 1005);
  abc := abc.(1 := 1003); // rhs optimized to just 1003
  gen := gen.(x := "<neg>");

  print r.u, " "; // 1062
  print g.x, " "; // 1063
  print rst.1, " "; // 1005
  print xyz.2, " "; // 1005
  print abc.1, " "; // 1003
  print gen.x, "\n"; // <gen>
}

method TestDiscriminators() {
  var r := SingletonRecord(62);
  var g := Compiled(63);
  var gen := GenericSingletonPlusGhost(1980, "<gen>");
  print r.SingletonRecord?, " ", g.Compiled?, " ", gen.GenericSingletonPlusGhost?, "\n"; // true true true
}

method TestMatchStmt() {
  var a := SingletonRecord(20);
  var b := Compiled(21);
  var c0 := (ghost 100, 101, a, ghost 103, 104);
  var c1 := (c0, ghost 200);
  var c := (ghost 300, c1);
  var gen := GenericSingletonPlusGhost(1980, "<gen>");

  match a {
    case SingletonRecord(u0) => print u0, " "; // 20
  }
  match a {
    case SingletonRecord(19) =>
    case SingletonRecord(u1) => print u1, " "; // 20
  }
  match a {
    case SingletonRecord(19) =>
    case SingletonRecord(20) => print "*20 "; // *20
    case SingletonRecord(_) =>
  }

  match b {
    case Compiled(v) => print v, " "; // 21
  }

  match c {
    case (g300, ((g100, h101, SingletonRecord(w), g103, h104), g200)) => print w, " "; // 20
  }

  match gen {
    case GenericSingletonPlusGhost(_, s) => print s, "\n"; // <gen>
  }
}

method TestMatchExpr() {
  var a := SingletonRecord(20);
  var b := Compiled(21);
  var c0 := (ghost 100, 101, a, ghost 103, 104);
  var c1 := (c0, ghost 200);
  var c := (ghost 300, c1);
  var gen := GenericSingletonPlusGhost(1980, "<gen>");

  print match a {
    case SingletonRecord(u0) => u0
  }, " "; // 20
  print match a {
    case SingletonRecord(19) => -1
    case SingletonRecord(u1) => u1
  }, " "; // 20
  print "*", match a {
    case SingletonRecord(19) => -1
    case SingletonRecord(20) => 20
    case SingletonRecord(_) => -1
  }, " "; // *20

  print match b {
    case Compiled(v) => v
  }, " "; // 21

  print match c {
    case (g300, ((g100, h101, SingletonRecord(w), g103, h104), g200)) => w
  }, " "; // 20

  print match gen {
    case GenericSingletonPlusGhost(_, s) => s
  }, "\n"; // <gen>
}

datatype Color = Pink | Gray | Green(int)
datatype AnotherSingletonRecord = AnotherSingletonRecord(color: Color)

datatype OneBool = OneBool(b: bool)

method TestEquality() {
  var r0 := SingletonRecord(62);
  var r1 := SingletonRecord(63);

  print r0 == r0, " ", r0 == r1, "\n"; // true false

  var s0 := AnotherSingletonRecord(Green(100));
  var s1 := AnotherSingletonRecord(Pink);
  var s2 := AnotherSingletonRecord(Green(100));
  var s3 := AnotherSingletonRecord(Green(101));

  print s0 == s0, " "; // true
  print s0 == s1, " "; // false
  print s0 == s2, " "; // true
  print s0 == s3, "\n"; // false

  var b0 := OneBool(false);
  var b1 := OneBool(true);
  print b0 == b0, " ", b0 == b1, "\n"; // false true
}

type Odd = x | x % 2 == 1 witness 13
datatype SingleOdd = SingleOdd(u: Odd)

datatype GenericSingle<X> = GenericSingle(x: X)
datatype GenericDouble<X, Y> = GenericDouble(x: X, y: Y)

type SX = (ghost int, bool, ghost int)
datatype SX4 = SX4(a: SX, ghost b: real) // represented as just bool

method TestDefaultValues<T(0), U(0)>() {
  var r: SingletonRecord;
  var xyz: (int, ghost int, int);
  var abc: (ghost int, int, ghost int);
  var klm: AnotherSingletonRecord;
  print r, " ", xyz, " ", abc, " ", klm, "\n"; // 0 (0, 0) 0 Color.Pink

  var odd: Odd;
  var s: SingleOdd;
  print odd, " ", s, " "; // 13 13

  var g1: GenericSingle<Odd>;
  var g2: GenericDouble<Odd, int>;
  print g1, " ", g2, " "; // 13 GenericDouble(13, 0)

  var t: T;
  var u: U;
  var sx4: SX4;
  print t, " ", u, " ", sx4, "\n"; // 0 13 false
}

method TestTypeParameters<X, Y, Z>(x: GenericGhostOrNot<X>, y: GenericGhostOrNot<Y>, z: Z) {
  print x, " ", y, " ", z, "\n"; // <gen> 3.14 2.7
}

datatype Memberful<T> = MakeMemberful(tt: T) {
  function method G<U>(t: T, u: U): (T, T, U) {
    (tt, t, u)
  }
  method M<U>(t: T, u: U) {
    print tt, " ", t, " ", u, "\n";
  }
}

// The following type is not optimized, because it has a const member
datatype HasConst<T> = MakeC(tt: T) {
  const u: (T, T) := (tt, tt)
}

// This type is similar to HasConst, but has a function instead of a const, so it is optimized
datatype HasFunction<T> = MakeF(tt: T) {
  function method F(): (T, T) {
    (tt, tt)
  }
}

method TestMembers() {
  var d := MakeMemberful(18.0);
  var (a, b, c) := d.G(3.0, false);
  print d, " ", a, " ", b, " ", c, "\n"; // 18.0 18.0 3.0 false
  d.M(4.0, true); // 18.0 4.0 true

  var h := MakeC(4 as bv7);
  print h, " ", h.u, "\n"; // MakeC(4) (4, 4)

  var f := MakeF(4 as bv7);
  print f, " ", f.F(), "\n"; // 4 (4, 4)
}

// --- Here are some test types to make sure DowncastClone methods are generated properly

datatype XCell<B, -Unused> = MakeXCell(xdata: B, ii: int)
datatype XList<X, Y> =
  | KKK(aa: XCell<X, int>)
  | LLL(bb: XList<X, Y>)

datatype Cell<B> = MakeCell(data: B)
datatype List<X, Y> =
  | AAA(aa: Cell<X>)
  | BBB(bb: List<X, Y>)
datatype MetaList<X, Y> =
  | MMM(mm: List<X, Y>)
  | NNN(nn: MetaList<X, Y>)

datatype SCell<B> = MakeSCell(sdata: seq<B>)
datatype SList<X, Y> =
  | RRR(rr: Cell<X>)
  | SSS(ss: List<X, Y>)
datatype SMetaList<X, Y> =
  | TTT(tt: List<X, Y>)
  | UUU(uu: MetaList<X, Y>)

// --------------------------------------------------------------------------------

module OptimizationChecks {
  // Not optimized
  datatype CyclicTypeIsNotErasableWrapper =
    | ghost Zero
    | Succ(CyclicTypeIsNotErasableWrapper)

  // Not optimized
  datatype Mutual0 =
    | ghost Zero
    | AboutToBecomeSucc(Mutual1)
  datatype Mutual1 =
    | HereIsTheSucc(Mutual0)

  // Optimized to just Mutual0
  datatype Lasso =
    | Lasso(m0: Mutual0)

  // Optimized to just MyClass
  datatype WrapperAroundMyClass = WAMC(MyClass)
  class MyClass {
    var w: WrapperAroundMyClass

    constructor () {
      w := WAMC(this);
    }
  }

  // Not optimized
  datatype ViaClass = ViaClass(Class<ViaClass>)
  class Class<Y> { }

  // Optimized to just ZClass
  datatype DDZ = DDZ(ZClass)
  trait ZParent<Z> { }
  class ZClass extends ZParent<DDZ> { }

  // Optimized to just X, whatever X is
  datatype WrapperOrGhost<X> =
    | Wrapper(X)
    | ghost Nothing

  datatype IntsWrapper = IntsWrapper(ints: Ints) // optimized
  datatype Ints = Ints(x: int, y: int) | AnotherIntsWrapper(wrapper: IntsWrapper)

  method Test() {
    var c;
    c := Succ(c);

    var m1;
    m1 := HereIsTheSucc(AboutToBecomeSucc(m1));
    var m0;
    m0 := AboutToBecomeSucc(m1);

    var l;
    l := Lasso(m0);

    var five := 5;

    var mc := new MyClass();
    var w;
    if five < 10 {
      w := WAMC(mc);
    }

    var vc := new Class<ViaClass>;
    var v;
    if five < 10 {
      v := ViaClass(vc);
    }

    var zc := new ZClass;
    var z;
    if five < 10 {
      z := DDZ(zc);
    }

    // In the following line, the verifier knows that w, v, and z have been initialized. However, C# does
    // not (because of the two "if five < 10" statements above. Thus, Dafny had better make sure these local
    // variables are initialized (to some placebo value).
    Call(w, v, z);

    var gw;
    gw := Wrapper(true);

    var gl: WrapperOrGhost<Lasso>; // compiled as Mutual0
    var gg0: WrapperOrGhost<WrapperOrGhost<Lasso>>; // compiled as Mutual0
    var gg1: WrapperOrGhost<WrapperOrGhost<Lasso>>; // compiled as Mutual0
    gg0 := Wrapper(gl);
    gl := Wrapper(l);
    gg1 := Wrapper(gl);

    var ii := Ints(5, 7);
    var wrapper := IntsWrapper(ii);
    var wwrapper := AnotherIntsWrapper(wrapper);
    print ii, " ", wrapper, " ", wwrapper, "\n"; // Ints(5, 7) Ints(5, 7) AnotherIntsWrapper(Ints(5, 7))
  }

  method Call(w: WrapperAroundMyClass, v: ViaClass, z: DDZ) { }

  // Technically, it would be possible to consider AA0 an erasable type wrapper, because
  // the type parameter UnusedTypeParameter is not used. However, detecting this case would
  // make the detection algorithm more complicated, so we opt not to detect this case.
  // (Note. The tests don't print these types, because they unavoidably involve uninitialized
  // values. We still include them here for the record, and to make sure that the compiler
  // doesn't crash on them.)
  datatype AA0 = AA0(BB0)
  datatype BB0 = BB0(CC0<AA0>)
  datatype CC0<UnusedTypeParameter> = CC0(BB0) | ghost NoCC0

  // For the record, here are some types where the type parameters make it impossible to erase
  // the datatype wrapper for A (for a target language that supports type parameters).
  datatype HA = HA(HB)
  datatype HB = HB0(HD<HA>) | ghost HB1
  datatype HD<X> = HD(X, HA)
}
