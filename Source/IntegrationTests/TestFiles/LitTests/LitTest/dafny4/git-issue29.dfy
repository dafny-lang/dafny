// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function Identity<T>(a:T) : T
{
  a
}

ghost function SeqIdentity<T>(s:seq<T>) : seq<T>
{
    s
}

ghost function ArrayIdentity<T>(a:array<T>) : array<T>
{
    a
}

type uint32 = i : int | 0 <= i < 0x1_0000_0000

lemma test()
{
    var x:uint32;
    var g := Identity(x);     // Works

    var s:seq<uint32>;
    var s' := Identity(s);      // Works
    var s'' := SeqIdentity(s);  // Works

    var a:array<uint32>;
    var a' := Identity(a);    // Works
    var a'' := ArrayIdentity(a);  // Error
}


ghost function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
ghost predicate WordSeqToBytes(ws:seq<uint32>)

method test2(M:seq<seq<uint32>>)
{
    ghost var t := WordSeqToBytes(ConcatenateSeqs(M));
}

