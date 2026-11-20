// RUN: %verify --rprint "%t.rprint.dfy" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%t.rprint.dfy" "%s"

// The trigger generator gives a quantifier that it does not split its triggers with the term that it names for the
// loop through s[i] and s[i + 1], and the refining module's copy gets both again, not the triggers without the name
// CHECK: forall i: int \{:split false\} /\*\{:_trigger s\[i \+ 1\], s\[i\]\}\*/ /\*\{:_named i \+ 1\}\*/ ::
// CHECK: forall i: int \{:split false\} /\*\{:_trigger s\[i \+ 1\], s\[i\]\}\*/ /\*\{:_named i \+ 1\}\*/ ::
abstract module A {
  lemma L(s: seq<int>)
    requires forall i {:split false} :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
    ensures |s| > 2 ==> s[0] <= s[2]
  {
    if |s| > 2 {
      assert s[0] <= s[1];
    }
  }
}

module B refines A {
}
