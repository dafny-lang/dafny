// RUN: %dafny /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

method Test1()
{
    var tuple0 := (ghost 0:=123, ghost 1:=234);
    var tuple1 := (ghost 123, ghost 234);
    assert tuple0 == tuple1;
}

method Test2()
{
    var tuple0 := (ghost 10:=10, 3:=3, 0:=0, 1:=1, 2:=2, 4:=4, 5:=5, 6:=6, 7:=7, 8:=8, 9:=9);
    var tuple1 := (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, ghost 10);
    assert tuple0 == tuple1;
}
