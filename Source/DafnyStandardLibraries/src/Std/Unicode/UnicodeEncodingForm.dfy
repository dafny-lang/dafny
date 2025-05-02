/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

/**
  * A Unicode encoding form assigns each Unicode scalar value to a unique code unit sequence.
  *
  * A concrete `UnicodeEncodingForm` MUST define the following:
  *  - The type `CodeUnit`.
  *  - The predicate `IsMinimalWellFormedCodeUnitSubsequence`, which defines the set of encodings of scalar values,
  *    known as "minimal well-formed code unit subsequences".
  *  - The function `SplitPrefixMinimalWellFormedCodeUnitSubsequence`, which defines the algorithm by which to parse
  *    a minimal well-formed code unit subsequence from the beginning of a code unit sequence.
  *  - The function `EncodeScalarValue`, which defines the mapping from scalar values to minimal well-formed code unit
  *    subsequences.
  *  - The function `DecodeMinimalWellFormedCodeUnitSubsequence`, which defines the mapping from minimal well-formed
  *    code unit subsequences to scalar values.
  */
abstract module Std.Unicode.UnicodeEncodingForm {
  import opened Wrappers
  import Strings

  import Functions
  import Collections.Seq
  import opened Base

  type CodeUnitSeq = seq<CodeUnit>
  type WellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsWellFormedCodeUnitSequence(s)
    witness []
  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *

  //
  // Begin abstract items.
  //

  /**
    * A code unit is the minimal bit combination that can represent a unit of encoded text for processing or
    * interchange. (Section 3.9 D77.)
    */
  type CodeUnit

  /**
    * A well-formed Unicode code unit sequence that maps to a single Unicode scalar value.
    * (Section 3.9 D85a.)
    */
  function IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==>
              && |s| > 0
              && forall i | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|

  /**
    * Returns the shortest prefix of `s` that is a minimal well-formed code unit subsequence,
    * or None if there is no such prefix.
    */
  function SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==>
            && maybePrefix.Some?
    ensures maybePrefix.Some? ==>
              && var prefix := maybePrefix.Extract();
              && 0 < |prefix| <= |s|
              && prefix == s[..|prefix|]
              && forall i | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])

  /**
    * Returns the minimal well-formed code unit subsequence that this encoding form assigns to the given scalar value.
    * The Unicode standard requires that this is injective.
    *
    * TODO: enforce that implementations satisfy Functions.Injective
    */
  function EncodeScalarValue(v: ScalarValue): (m: MinimalWellFormedCodeUnitSeq)

  /**
    * Returns the scalar value that this encoding form assigns to the given minimal well-formed code unit subsequence.
    */
  function DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: ScalarValue)
    ensures EncodeScalarValue(v) == m

  //
  // End abstract items.
  //

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
        if m1 < m2 {
          assert false by { assert m1 == m2[..|m1|]; }
        }
      }
    }
  }

  /**
    * If `ms` is the concatenation of a minimal well-formed code unit subsequence `m` and a code unit sequence `s`,
    * then the shortest minimal well-formed code unit subsequence prefix of `ms` is simply `m`.
    */
  lemma LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m: MinimalWellFormedCodeUnitSeq, s: CodeUnitSeq)
    ensures SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + s) == Some(m)
  {
    var ms := m + s;
    var maybePrefix := SplitPrefixMinimalWellFormedCodeUnitSubsequence(ms);
    assert maybePrefix.Some? by { assert IsMinimalWellFormedCodeUnitSubsequence(ms[..|m|]); }
    var prefix := maybePrefix.Extract();

    assert m <= ms;
    assert prefix <= ms;
    LemmaUniquePrefixMinimalWellFormedCodeUnitSeq(ms, m, prefix);
  }

  /**
    * Returns the unique partition of the given code unit sequence into minimal well-formed code unit subsequences,
    * or Failure(CodeUnitSeq) if no such partition exists, where the resulting sequence is the suffix it could not partition.
    */
  function PartitionCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeParts: Result<seq<MinimalWellFormedCodeUnitSeq>, CodeUnitSeq>)
    ensures maybeParts.Success? ==> Seq.Flatten(maybeParts.Extract()) == s
    decreases |s|
  {
    if s == [] then Success([])
    else
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(s).ToResult(s);
      // Recursing/iterating on subsequences leads to quadratic running time in most/all Dafny runtimes as of this writing.
      // This definition (and others in the Unicode modules) emphasizes clarity and correctness,
      // and while the by-method implementation avoids stack overflows due to non-tail-recursive recursion,
      // it doesn't yet avoid the subsequences.
      // The best solution would be to ensure all Dafny runtimes implement subsequences as an O(1)
      // operation, so this implementation would become linear.
      var restParts :- PartitionCodeUnitSequenceChecked(s[|prefix|..]);
      Success([prefix] + restParts)
  } by method {
    if s == [] {
      return Success([]);
    }
    var result: seq<MinimalWellFormedCodeUnitSeq> := [];
    var rest := s;
    while |rest| > 0
      invariant PartitionCodeUnitSequenceChecked(s).Success?
           <==> PartitionCodeUnitSequenceChecked(rest).Success?
      invariant
        if PartitionCodeUnitSequenceChecked(s).Success? then
          && PartitionCodeUnitSequenceChecked(s).value
             == result + PartitionCodeUnitSequenceChecked(rest).value
        else
          PartitionCodeUnitSequenceChecked(s).error == PartitionCodeUnitSequenceChecked(rest).error
    {
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(rest).ToResult(rest);
      result := result + [prefix];
      rest := rest[|prefix|..];
    }
    assert result + [] == result;
    return Success(result);
  }

  /**
    * Returns the unique partition of the given well-formed code unit sequence into minimal well-formed code unit
    * subsequences.
    */
  function PartitionCodeUnitSequence(s: WellFormedCodeUnitSeq): (parts: seq<MinimalWellFormedCodeUnitSeq>)
    ensures Seq.Flatten(parts) == s
  {
    PartitionCodeUnitSequenceChecked(s).Extract()
  }

  /**
    * The partitioning of a minimal well-formed code unit subsequence is the singleton sequence
    * containing exactly the minimal well-formed code unit subsequence.
    */
  lemma LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq)
    ensures PartitionCodeUnitSequenceChecked(m) == Success([m])
  {
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, []);
    calc == {
      Success(m);
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + []).ToResult(m);
      { assert m + [] == m; }
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m).ToResult(m);
    }
    calc == {
      PartitionCodeUnitSequenceChecked(m);
      Success([m] + []);
      { assert [m] + [] == [m]; }
      Success([m]);
    }
  }

  /**
    * A code unit sequence is well-formed iff it can be partitioned into a sequence of minimal well-formed code unit subsequences.
    */
  function IsWellFormedCodeUnitSequence(s: CodeUnitSeq): (b: bool)
  {
    PartitionCodeUnitSequenceChecked(s).Success?
  }

  /**
    * A minimal well-formed code unit subsequence is a well-formed code unit sequence.
    */
  lemma LemmaMinimalWellFormedCodeUnitSubsequenceIsWellFormedSequence(m: MinimalWellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m)
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
  }

  /**
    * The concatenation of a minimal well-formed code unit subsequence and a well-formed code unit sequence
    * is itself a well-formed code unit sequence.
    */
  lemma LemmaPrependMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq, s: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m + s)
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, s);
  }

  /**
    * The concatenation of minimal well-formed code unit subsequences is itself a well-formed code unit sequence.
    */
  lemma LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms: seq<MinimalWellFormedCodeUnitSeq>)
    ensures IsWellFormedCodeUnitSequence(Seq.Flatten(ms))
  {
    if |ms| == 0 {
      // assert IsWellFormedCodeUnitSequence(Seq.Flatten(ms));
    }
    else {
      var head := ms[0];
      var tail := ms[1..];
      LemmaFlattenMinimalWellFormedCodeUnitSubsequences(tail);
      var flatTail := Seq.Flatten(tail);
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(head, flatTail);
    }
  }

  /**
    * The concatenation of well-formed code unit sequences is itself a well-formed code unit sequence.
    */
  lemma LemmaConcatWellFormedCodeUnitSubsequences(s: WellFormedCodeUnitSeq, t: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(s + t)
  {
    var partsS := PartitionCodeUnitSequence(s);
    var partsT := PartitionCodeUnitSequence(t);
    var partsST := partsS + partsT;
    Seq.LemmaFlattenConcat(partsS, partsT);

    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(partsST);
  }

  /**
    * Returns the well-formed Unicode string that is the encoding of the given scalar value sequence.
    */
  function EncodeScalarSequence(vs: seq<ScalarValue>): (s: WellFormedCodeUnitSeq)
  {
    var ms := Seq.Map(EncodeScalarValue, vs);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms);
    Seq.Flatten(ms)
  }
  by method {
    // Optimize to to avoid allocating the intermediate unflattened sequence.
    // We can't quite use Seq.FlatMap easily because we need to prove the result
    // is not just a seq<CodeUnit> but a WellFormedCodeUnitSeqs.
    // TODO: We can be even more efficient by using a JSON.Utils.Vectors.Vector instead.
    s := [];
    ghost var unflattened: seq<MinimalWellFormedCodeUnitSeq> := [];
    for i := |vs| downto 0
      invariant unflattened == Seq.MapPartialFunction(EncodeScalarValue, vs[i..])
      invariant s == Seq.Flatten(unflattened)
    {
      var next: MinimalWellFormedCodeUnitSeq := EncodeScalarValue(vs[i]);
      unflattened := [next] + unflattened;
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(next, s);
      s := next + s;
    }
  }

  /**
    * Returns the scalar value sequence encoded by the given well-formed Unicode string.
    */
  function DecodeCodeUnitSequence(s: WellFormedCodeUnitSeq): (vs: seq<ScalarValue>)
    ensures EncodeScalarSequence(vs) == s
  {
    var parts := PartitionCodeUnitSequence(s);
    var vs := Seq.MapPartialFunction(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      { assert parts == Seq.MapPartialFunction(EncodeScalarValue, vs); }
      Seq.Flatten(Seq.MapPartialFunction(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    vs
  }

  function DecodeErrorMessage(index: int): string {
    "Could not decode byte at index " + Strings.OfInt(index)
  }

  /**
    * Returns the scalar value sequence encoded by the given code unit sequence, or Failure if the given Unicode string
    * is not well-formed.
    */
  function DecodeCodeUnitSequenceChecked(s: CodeUnitSeq): (resultVs: Result<seq<ScalarValue>, string>)
    ensures IsWellFormedCodeUnitSequence(s) ==>
              && resultVs.Success?
              && resultVs.Extract() == DecodeCodeUnitSequence(s)
    ensures !IsWellFormedCodeUnitSequence(s) ==> && resultVs.Failure?
  {
    // IsWellFormedCodeUnitSequence and DecodeCodeUnitSequence each call PartitionCodeUnitSequence,
    // so for efficiency we avoid recomputing the partition in the by-method.
    match PartitionCodeUnitSequenceChecked(s) {
      case Success(_) => Success(DecodeCodeUnitSequence(s))
      case Failure(s') => Failure(DecodeErrorMessage(|s|-|s'|))
    }
  }
  by method {
    var maybeParts := PartitionCodeUnitSequenceChecked(s);
    if maybeParts.Failure? {
      return Failure(DecodeErrorMessage(|s|-|maybeParts.error|));
    }
    var parts := maybeParts.value;
    var vs := Seq.MapPartialFunction(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      { assert parts == Seq.MapPartialFunction(EncodeScalarValue, vs); }
      Seq.Flatten(Seq.MapPartialFunction(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    return Success(vs);
  }
}
