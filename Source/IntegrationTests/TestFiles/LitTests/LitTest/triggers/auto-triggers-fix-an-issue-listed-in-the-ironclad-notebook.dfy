// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This example was listed in IronClad's notebook as one place were z3 picked
// much too liberal triggers. THe Boogie code for this is shown below:
//
// forall k#2: Seq Box :: $Is(k#2, TSeq(TInt)) && $IsAlloc(k#2, TSeq(TInt), $Heap)
//                   ==> Seq#Equal(_module.__default.HashtableLookup($Heap, h1#0, k#2),
//                                 _module.__default.HashtableLookup($Heap, h2#0, k#2))
//
// and z3 would pick $Is(k#2, TSeq(TInt)) or $IsAlloc(k#2, TSeq(TInt), $Heap) as
// triggers.

type Key = seq<int>
type Value = seq<int>

type Hashtable = map<Key, Value>
ghost function HashtableLookup(h: Hashtable, k: Key): Value

lemma HashtableAgreement(h1:Hashtable, h2:Hashtable, k:Key)
  requires forall k :: HashtableLookup(h1,k) == HashtableLookup(h2,k) {
    assert true || (k in h1) == (k in h2);
}
