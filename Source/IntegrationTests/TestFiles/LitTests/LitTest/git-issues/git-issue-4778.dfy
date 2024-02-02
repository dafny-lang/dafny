// RUN: %verify --warn-contradictory-assumptions "%s" > "%t"
// DIFF: "%s.expect" "%t"

type CodeUnit
type CodeUnitSeq = seq<CodeUnit>
type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
  | IsMinimalWellFormedCodeUnitSubsequence(s)
  witness *

function IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
  ensures b ==>
            && |s| > 0
            && forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
  decreases |s|

/**
 * If minimal well-formed code unique subsequences `m1` and `m2` are prefixes of `s`, then they are equal.
 */
lemma LemmaUniquePrefixMinimalWellFormedCodeUnitSeq(
  s: CodeUnitSeq, m1: MinimalWellFormedCodeUnitSeq, m2: MinimalWellFormedCodeUnitSeq
)
  decreases |s|, |m1|, |m2|
  requires m1 <= s
  requires m2 <= s
  ensures m1 == m2
{
  // Handle only the |m1| <= |m2| case explicitly
  if |m1| > |m2| {
    LemmaUniquePrefixMinimalWellFormedCodeUnitSeq(s, m2, m1);
  } else {
    assert m1 <= m2;
    assert m1 == m2 by {
      var m2' := m2[..|m1|];
      if m1 < m2 {
        assert {:contradiction} m1 == m2';
      }
    }
  }
}
