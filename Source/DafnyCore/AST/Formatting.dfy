/// Microsoft.Dafny.Formatting.ReindentProgramFromFirstToken() takes
/// - A first token, from which an entire program is available
/// - A IIndentationFormatter, that knows how to indent every token
/// It then prints every token (proven) in order, reindenting its leading trivia and trailing trivia

module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  class {:extern "Text.StringBuilder"} {:compile false} CsStringBuilder {
    ghost var built: CsString
    constructor {:extern} ()
    method {:extern "Append"} Append(s: CsString)
      modifies this
      ensures built == String.Concat(old(built), s)
    // This hack is necessary because ToString is replaced by ToString_
    // in the C# compiler, even if it's declared extern...
    method {:extern @"ToString().ToString"} ToString() returns (r: CsString)
      ensures r == built
  }
  type {:extern "String"} CsString(!new,==) {
    ghost predicate {:extern} Contains(needle: CsString)
    lemma {:axiom} ContainsTransitive(other: CsString, needle: CsString)
      requires Contains(other) && other.Contains(needle)
      ensures Contains(needle)
  }
  lemma ContainsTransitive()
    ensures forall s1: CsString, s2: CsString, s3: CsString
              | s1.Contains(s2) && s2.Contains(s3) :: s1.Contains(s3)
  {
    forall s1: CsString, s2: CsString, s3: CsString
      | s1.Contains(s2) && s2.Contains(s3)
    {
      s1.ContainsTransitive(s2, s3);
    }
  }
  class {:extern "String"} {:compile false} String {
    static function Concat(s1: CsString, s2: CsString): (r: CsString)
      ensures r.Contains(s1)
      ensures r.Contains(s2)
  }
}

module {:extern "Microsoft.Dafny"} {:compile false} {:options "-functionSyntax:4"} MicrosoftDafny {
  import opened System

  trait {:extern "IToken"} {:compile false} IToken {
    var val : CsString
    var LeadingTrivia: CsString
    var TrailingTrivia: CsString
    var Next: IToken?
    ghost var allTokens: seq<IToken>

    ghost predicate Valid() reads this, allTokens decreases |allTokens| {
      && |allTokens| > 0 && allTokens[0] == this
      && (|| (|allTokens| == 1 && Next == null)
          || (&& |allTokens| > 1
              && Next == allTokens[1]
              && Next.allTokens == allTokens[1..]
              && Next.Valid())
         )
    }
    lemma AlltokenSpec(i: int)
      requires Valid()
      decreases |allTokens|
      requires 0 <= i < |allTokens|
      ensures allTokens == allTokens[..i] + allTokens[i].allTokens
    {
      if i == 0 {
      } else {
        this.Next.AlltokenSpec(i - 1);
      }
    }
    lemma TokenNextIsIPlus1(middle: IToken, i: int)
      requires Valid()
      requires 0 <= i < |allTokens|
      requires allTokens[i] == middle;
      requires middle.Next != null
      ensures 0 <= i + 1 < |allTokens| && allTokens[i+1] == middle.Next
    {
      if i == 0 {
      } else {
        this.Next.TokenNextIsIPlus1(middle, i - 1);
      }
    }

    lemma TokenNextIsNullImpliesLastToken(middle: IToken, i: int)
      requires middle.Valid() && this.Valid()
      requires 0 <= i < |allTokens|
      requires middle == allTokens[i]
      requires middle.Next == null
      ensures i == |allTokens|-1
    {
      if Next == null {
      } else {
        Next.TokenNextIsNullImpliesLastToken(middle, i-1);
      }
    }
  }
}