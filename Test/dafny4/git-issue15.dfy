// RUN: %dafny  /compile:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype obj = Obj(fooBar:map<foo,int>)
datatype foo = Foo

method test_case() returns (o:obj)
{
    if true {
        o:= o.(fooBar := o.fooBar[Foo := 3]);
    }
}