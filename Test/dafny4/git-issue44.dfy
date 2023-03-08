// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type uint32 = i:int | 0 <= i < 0x1_0000_0000

ghost function RepeatValue<T>(n:T, count:nat) : seq<T>

ghost function RepeatMapValue<T>(n:T, count:nat) : map<T, T>

ghost function RepeatArrayValue<T>(n:T, count:nat) : array<T>

ghost function Example1(len:nat) : seq<uint32>
{
    // Error: value does not satisfy the subset constraints of 'seq<uint32>'
    RepeatValue(5 as uint32, len)
}

ghost function Example2(len:nat) : map<uint32, uint32>
{
    RepeatMapValue(5 as uint32, len)
}

ghost function Example3(len:nat) : array<uint32>
{
    RepeatArrayValue(5 as uint32, len)
}