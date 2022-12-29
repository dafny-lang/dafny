// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type uint32 = i:int | 0 <= i < 0x1_0000_0000

function RepeatValue<T>(n:T, count:nat) : seq<T>

function RepeatMapValue<T>(n:T, count:nat) : map<T, T>

function RepeatArrayValue<T>(n:T, count:nat) : array<T>

function Example1(len:nat) : seq<uint32>
{
    // Error: value does not satisfy the subset constraints of 'seq<uint32>'
    RepeatValue(5 as uint32, len)
}

function Example2(len:nat) : map<uint32, uint32>
{
    RepeatMapValue(5 as uint32, len)
}

function Example3(len:nat) : array<uint32>
{
    RepeatArrayValue(5 as uint32, len)
}
