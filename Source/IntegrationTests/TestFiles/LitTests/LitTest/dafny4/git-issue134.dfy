// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


lemma MapValues()
    ensures false
{
    var m := map[0 := false];
    assert m.Keys == {0};
    assert m.Values == {false};

    var m' := m[0 := true];

    assert m'.Values == m.Values + {true};  // This was once a bug in the axiomatization of maps
    assert m'.Values == {true};
    assert false;
}
