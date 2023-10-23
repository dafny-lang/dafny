// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type word = x | 0 <= x < 0x1_0000_0000

ghost function extract(src:map<int, word>): map<int, word>
    requires forall i :: 0 <= i < 0x10 ==> i in src
{
    (map i | 0 <= i < 0x10 :: src[i])
}

