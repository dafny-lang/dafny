// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module MainStuff {
  datatype MyDataType = MyConstructor(myint:int, mybool:bool)
                      | MyOtherConstructor(otherbool:bool)
                      | MyNumericConstructor(42:int)
  datatype SomeOtherType = S_O_T(non_destructor: int)

  method test(foo:MyDataType, x:int) returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires foo.MyConstructor?
    ensures abc == foo.(myint := x + 2)
    ensures jkl == foo.(non_destructor := 5)      // error: 'non_destructor' is not a destructor in MyDataType
    ensures jkl == foo.(mybool := true, 40 := 100, myint := 200)  // error: '40' is not a destructor
  {
    abc := MyConstructor(x + 2, foo.mybool).(myint := x + 3);
    abc := foo.(myint := x + 2, mybool := true).(mybool := false);  // allowed
    def := MyOtherConstructor(!foo.mybool).(otherbool := true, otherbool := true);  // error: duplicated member
    ghi := MyConstructor(2, false).(otherbool := true);  // allowed, and will generate verification error
    jkl := foo.(42 := 7, otherbool := true);  // error: members are from different constructors
  }

  datatype Dt = Make(x: int)

  method Main()
  {
    var d := Make(5);
    d := d.(x := 20);
    d := d.(Make? := d);  // error: Make? is not a destructor (this previously crashed the resolver)
  }

  module Issue214Regression {
    datatype GenericType<T> = GenericType(value:T)

    type ConcreteType = GenericType<int>

    function F(c:ConcreteType): ConcreteType {
      c.(value := 0)
    }

    function G(): int {
      ConcreteType.GenericType(5).value
    }
  }
}

module GhostExpressions {
  datatype R = R(x: int, ghost y: int)

  // source is ghost
  method Test0(ghost r: R, g: int) returns (b: R) {
    var a := r.(x := g); // the use of r makes RHS ghost
    b := a; // error: RHS is ghost, LHS is not

    b := r.(x := g); // error: RHS is ghost, LHS is not
  }

  // new value is ghost
  method Test1(r: R, ghost g: int, h: int) returns (b: R) {
    var a := r.(x := g); // the use of g makes RHS ghost
    b := a; // error: RHS is ghost, LHS is not

    b := r.(x := g); // error: RHS is ghost, LHS is not

    var c := r.(y := g);
    b := c;
    b := r.(y := g);

    var d := if r.x == 3 then r.(x := g, y := h) else r.(y := h, x := g); // the use of g makes RHS ghost
    b := d; // error: RHS is ghost, LHS is not
    b := r.(x := g, y := h); // error: RHS is ghost, LHS is not
    b := r.(y := h, x := g); // error: RHS is ghost, LHS is not

    var e := if r.x == 3 then r.(x := h, y := g) else r.(y := g, x := h);
    b := e;
    b := r.(x := h, y := g);
    b := r.(y := g, x := h);
  }

  // field is ghost
  method Test2(r: R, g: int) returns (b: R) {
    // In the following, since y is ghost, the update operations are really just no-ops in the compiled code.
    var a := r.(y := g);
    b := a;

    b := r.(y := g);
  }

  // one of the fields is ghost
  method Test3(r: R, g: int) returns (b: R) {
    // In the following, since y is ghost, the updates of y are really just no-ops in the compiled code.
    var a := if g == 3 then r.(x := g, y := g) else r.(y := g, x := g);
    b := a;

    b := r.(x := g, y := g);
    b := r.(y := g, x := g);
  }
}
