// RUN: %dafny /compile:0 /dprint:- "%s" > "%t"


method Test()
{
    var f: ((int,int)) -> int := (x: (int,int)) => 1;
}

