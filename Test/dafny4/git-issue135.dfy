// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma lemma_MapTest()
    ensures false
{
    var m := map [ 1 := 1, 2 := 1 ];
    assert m.Keys == {1, 2};
    assert m.Values == {1};
    assert |m| == |m.Keys| == 2;
    assert |m| == |m.Values| == 1;  // This was once a bug in the axiomatization of maps
    assert 1 == 2;
    assert false;
}
