// RUN: %dafny /compile:0 /env:0 /dprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test()
{
    var f: ((int,int)) -> int := (x: (int,int)) => 1;
}

