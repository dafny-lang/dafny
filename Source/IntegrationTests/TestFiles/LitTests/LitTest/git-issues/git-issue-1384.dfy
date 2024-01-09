// RUN: %testDafnyForEachResolver "%s" -- --print:-


method Test()
{
    var f: ((int,int)) -> int := (x: (int,int)) => 1;
}

