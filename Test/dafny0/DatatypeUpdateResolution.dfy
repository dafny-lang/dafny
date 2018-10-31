// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
