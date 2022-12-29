// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type uint32 = i:int | 0 <= i < 0x1_0000_0000

function last<T>(s:seq<T>):T
    requires |s| > 0;
{
    s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
    requires |s| > 0;
    ensures  |all_but_last(s)| == |s| - 1;
{
    s[..|s|-1]
}

function ConcatenateSeqs<T>(ss:seq<seq<T>>) : seq<T>
{
    if |ss| == 0 then [] else ss[0] + ConcatenateSeqs(ss[1..])
}

lemma {:axiom} lemma_ReverseConcatenateSeqs<T>(ss:seq<seq<T>>)
    requires |ss| > 0;
    ensures  ConcatenateSeqs(ss) == ConcatenateSeqs(all_but_last(ss)) + last(ss);

lemma Test(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];

    calc {
        ConcatenateSeqs(word_seqs');
            { lemma_ReverseConcatenateSeqs(word_seqs'); }
        ConcatenateSeqs(all_but_last(word_seqs')) + last(word_seqs');
    }
}

lemma AltTest(word_seqs:seq<seq<uint32>>, words:seq<uint32>)
{
    var word_seqs' := word_seqs + [words];
    assert last(word_seqs') == words;
    assert ConcatenateSeqs(word_seqs) + last(word_seqs') == ConcatenateSeqs(word_seqs) + words;
}

function f<T>(s:seq<T>):seq<T>

function g<T>(ss:seq<seq<T>>) : seq<T>

lemma {:axiom} lemma_fg<T>(s:seq<seq<T>>)
    ensures  g(s) == g(f(s));

lemma Test2(s:seq<seq<uint32>>)
{
    calc {
        g(s);
            { lemma_fg(s); }
        g(f(s));
    }
}

lemma AltTest2(s:seq<seq<uint32>>)
{
    lemma_fg(s);
    assert g(s) == g(f(s));
}

