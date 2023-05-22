// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NewSyntax {
  datatype MyDataType = MyConstructor(myint:int, mybool:bool)
                      | MyOtherConstructor(otherbool:bool)
                      | MyNumericConstructor(42:int)

  method test(foo:MyDataType, goo:MyDataType, hoo:MyDataType, x:int)
      returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires foo.MyConstructor? && goo.MyOtherConstructor? && hoo.MyNumericConstructor?
    ensures abc == foo.(myint := x + 2);
    ensures def == goo.(otherbool := !foo.mybool);
    ensures ghi == foo.(myint := 2).(mybool := false);
    ensures jkl == hoo.(42 := 7);
  {
    abc := MyConstructor(x + 4, foo.mybool);
    abc := abc.(myint := abc.myint - 2);
    def := MyOtherConstructor(!foo.mybool);
    ghi := MyConstructor(2, false);
    jkl := hoo.(42 := 7);

    assert abc.(myint := abc.myint - 2) == foo.(myint := x);
  }

  // regression test (for a previous bug in the Translator.Substituter):
  datatype Dt = Ctor(x: int, y: bool)
  ghost function F(d: Dt): Dt
  {
    d.(x := 5)
  }

  datatype NumericNames = NumNam(010: int, 10: real, f: bool)

  method UpdateNumNam(nn: NumericNames, y: int) returns (pp: NumericNames)
    ensures pp.10 == nn.10 && pp.010 == y
  {
    pp := nn.(010 := y);  // not to be confused with a field name 10
  }

  method MultipleUpdates(nn: NumericNames, y: int) returns (pp: NumericNames)
    ensures pp.010 == y
  {
    if * {
      pp := nn.(10 := 0.10, 010 := y);
    } else {
      pp := nn.(010 := y, f := true, 10 := 0.10);
    }
  }

  datatype Datte<T> = AA(a: int, x: int) | BB(b: bool, x: int) | CC(c: real) | DD(x: int, o: set<int>, p: bv27, q: T)
  method Matte(d: Datte<real>)
    requires !d.CC?
  {
    var s := d.(x := 5);
    assert
      (d.AA? && s == AA(d.a, 5)) ||
      (d.BB? && (s == BB(false, 5) || s == BB(true, 5))) ||
      (d.DD? && s.(x := d.x) == d.(p := d.p));
    if s.DD? {
      s := d.(q := 2.2, x := 3);
    }
    assert s.x == 5 || s.x == 3;
    assert s.x < 4 ==> s.DD?;
    assert s != CC(4.0);
    if * {
      assert s.b ==> s.BB?;  // error: cannot mention b unless s is a BB
    } else {
      assert s.(b := true).b;  // error: cannot mention b unless s is a BB
    }
  }
}

module Regression0 {
  datatype SystemState = SS(connections: map<int,Connection>)
  datatype Connection = C(acceptor: Actor)
  type Actor

  method M(ls: SystemState, actor: Actor, conn_id: int)
    requires conn_id in ls.connections
  {
    var x := ls.connections[conn_id];
    var y := x.(acceptor := actor);
  }
}
