// RUN: %dafny /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

method Test1()
{
    var t := (123, ghost 1:=234); // error: mixing named and positional tuple arguments is not allowed
}

method Test2()
{
    var first := 0;
    var t := (ghost first:=123, 1:=234); // error: the name of tuple arguments must be an integer
}

method Test3()
{
    var t := (1:=123, 2:=234); // error: the name of tuple argument must describe a valid position in the tuple, starting from zero
}

method Test4()
{
    var t := (1:=123, 1:=234); // error: different tuple arguments cannot have the same name
}

method Test5()
{
    var (ghost x) := 123; // syntax error
}
