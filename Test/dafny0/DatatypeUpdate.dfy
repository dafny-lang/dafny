// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module OldSyntax {
datatype MyDataType = MyConstructor(myint:int, mybool:bool) 
                    | MyOtherConstructor(otherbool:bool) 
                    | MyNumericConstructor(42:int)

method test(foo:MyDataType, x:int) returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires foo.MyConstructor?;
    ensures abc == foo.(myint := x + 2);
    ensures def == foo.(otherbool := !foo.mybool);
    ensures ghi == foo.(myint := 2).(mybool := false);
    //ensures jkl == foo.(non_destructor := 5);      // Resolution error: no non_destructor in MyDataType
    ensures jkl == foo.(42 := 7);
{
    abc := MyConstructor(x + 2, foo.mybool); 
    abc := foo.(myint := x + 2);
    def := MyOtherConstructor(!foo.mybool);
    ghi := MyConstructor(2, false);
    jkl := foo.(42 := 7);

    assert abc.(myint := abc.myint - 2) == foo.(myint := x);
}

// regression test (for a previous bug in the Translator.Substituter):
datatype Dt = Ctor(x: int, y: bool)
function F(d: Dt): Dt
{
  d.(x := 5)
}

datatype NumericNames = NumNam(010: int)

method UpdateNumNam(nn: NumericNames, y: int) returns (pp: NumericNames)
{
  pp := nn.(010 := y);  // not to be confused with a field name 10
}
}

module NewSyntax {
datatype MyDataType = MyConstructor(myint:int, mybool:bool) 
                    | MyOtherConstructor(otherbool:bool) 
                    | MyNumericConstructor(42:int)

method test(foo:MyDataType, x:int) returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires foo.MyConstructor?;
    ensures abc == foo.(myint := x + 2);
    ensures def == foo.(otherbool := !foo.mybool);
    ensures ghi == foo.(myint := 2).(mybool := false);
    //ensures jkl == foo.(non_destructor := 5);      // Resolution error: no non_destructor in MyDataType
    ensures jkl == foo.(42 := 7);
{
    abc := MyConstructor(x + 2, foo.mybool); 
    abc := foo.(myint := x + 2);
    def := MyOtherConstructor(!foo.mybool);
    ghi := MyConstructor(2, false);
    jkl := foo.(42 := 7);

    assert abc.(myint := abc.myint - 2) == foo.(myint := x);
}

// regression test (for a previous bug in the Translator.Substituter):
datatype Dt = Ctor(x: int, y: bool)
function F(d: Dt): Dt
{
  d.(x := 5)
}

datatype NumericNames = NumNam(010: int, 10: real, f: bool)

method UpdateNumNam(nn: NumericNames, y: int) returns (pp: NumericNames)
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
}
