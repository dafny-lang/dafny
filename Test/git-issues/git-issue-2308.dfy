// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} f(t: int): int { t }
function summarize(input: map<int, int>): int { |input| }

lemma lemme(input: map<int, int>, i: int, m: map<int, int>) {
    reveal f();
    assert  i == summarize(map k <- input :: f(k));
    assert  i == summarize(map k <- input :: f(k));
}