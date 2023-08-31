// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Fuel {
    ghost function FunctionA(x:int) : int
    {
        x + 2
    }

    ghost function FunctionB(y:int) : int
    {
        FunctionA(y - 2)
    }

		method {:fuel FunctionA,0,0}  MethodX(z:int)
    {
        assert FunctionB(z) == z; // error: Cannot see the body of FunctionA
    }
}

module Opaque {
    ghost function {:opaque} FunctionA(x:int) : int
    {
        x + 2
    }

    ghost function FunctionB(y:int) : int
    {
        FunctionA(y - 2)
    }

    method MethodX(z:int)
    {
        assert FunctionB(z) == z;
    }
}

