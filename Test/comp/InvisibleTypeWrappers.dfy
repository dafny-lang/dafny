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
  print t, " ", u, "\n"; // 0 13
}

method TestTypeParameters<X, Y, Z>(x: GenericGhostOrNot<X>, y: GenericGhostOrNot<Y>, z: Z) {
  print x, " ", y, " ", z, "\n"; // <gen> 3.14 2.7
}
