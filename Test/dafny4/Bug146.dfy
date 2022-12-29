// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method inhabited(world: array2<bool>): bool
{
    exists i,j :: 0 <= i < world.Length0 && 0 <= j < world.Length1 && world[i,j]  // error: insufficient reads clause
}
method GameOfLife(size: nat, N: nat)
    requires 0 < size
{
    var world := new bool[size,size];
    var n := 0;
    while inhabited(world) && n < N {
        forall i,j | 0 <= i < size && 0 <= j < size {
            world[i,j] := false;
        }
        assert inhabited(world); // the assert is verified due to lack of reads on method inhabited()
        // ...
        n := n + 1;
    }
}

function method inhabited2(world: array2<bool>): bool
    reads world
{
    exists i,j :: 0 <= i < world.Length0 && 0 <= j < world.Length1 && world[i,j]
}
method GameOfLife2(size: nat, N: nat)
    requires 0 < size
{
    var world := new bool[size,size];
    var n := 0;
    while inhabited2(world) && n < N {
        forall i,j | 0 <= i < size && 0 <= j < size {
            world[i,j] := false;
        }
        assert inhabited2(world); // error: everything is now "false"
        // ...
        n := n + 1;
    }
}
