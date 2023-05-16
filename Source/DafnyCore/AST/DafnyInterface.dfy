include "System.dfy"

// Interface with existing Dafny code (IToken)
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
  class {:extern "TriviaFormatterHelper"} {:compile false} TriviaFormatterHelper {
    static predicate EndsWithNewline(input: CsString)
  }
}
