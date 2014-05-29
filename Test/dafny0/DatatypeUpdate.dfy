// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype MyDataType = MyConstructor(myint:int, mybool:bool) 
                    | MyOtherConstructor(otherbool:bool) 
                    | MyNumericConstructor(42:int);

method test(foo:MyDataType, x:int) returns (abc:MyDataType, def:MyDataType, ghi:MyDataType, jkl:MyDataType)
    requires foo.MyConstructor?;
    ensures abc == foo[myint := x + 2];
    ensures def == foo[otherbool := !foo.mybool];
    ensures ghi == foo[myint := 2][mybool := false];
    //ensures jkl == foo[non_destructor := 5];      // Resolution error: no non_destructor in MyDataType
    ensures jkl == foo[42 := 7];
{
    abc := MyConstructor(x + 2, foo.mybool); 
    abc := foo[myint := x + 2];
    def := MyOtherConstructor(!foo.mybool);
    ghi := MyConstructor(2, false);
    jkl := foo[42 := 7];

    assert abc[myint := abc.myint - 2] == foo[myint := x];
}
