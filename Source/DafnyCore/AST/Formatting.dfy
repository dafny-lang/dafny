
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
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
  class {:extern "HelperString"} {:compile false} HelperString {
    static predicate FinishesByNewline(input: CsString)
  }
}
module {:extern "Microsoft"} {:options "-functionSyntax:4"}  Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "Formatting"} Formatting {
      import opened MicrosoftDafny
      import opened System

      const {:extern "System", "String.Empty"} CsStringEmpty: CsString;

      trait IIndentationFormatter {
        function Reindent(token: IToken, trailingTrivia: bool, precededByNewline: bool, indentation: CsString, lastIndentation: CsString): CsString
        method GetIndentation(token: IToken, currentIndentation: CsString)
          returns (
            indentationBefore: CsString,
            indentationBeforeSet: bool,
            lastIndentation: CsString,
            lastIndentationSet: bool,
            indentationAfter: CsString,
            indentationAfterSet: bool)
          requires token.Valid()
          ensures token.allTokens == old(token.allTokens)
      }

      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {
      }

      /** Prints the entire program while fixing identation, based on
          1) indentation information provided by the IIndentationFormatter reindent
          2) Reindentation algorithm provided by the same reindent */
      method printSourceReindent(firstToken: IToken, reindent: IIndentationFormatter) returns (s: CsString)
        requires firstToken.Valid()
        ensures forall token <- firstToken.allTokens :: s.Contains(token.val)
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        var currentIndent := CsStringEmpty;
        ghost var i := 0;
        var leadingTriviaWasPreceededByNewline := true;
        var allTokens := firstToken.allTokens;
        while(token != null)
          decreases if token == null then 0 else |token.allTokens|
          invariant 0 <= i <= |allTokens|
          invariant if token == null then i == |allTokens| else
                    && token.Valid()
                    && i < |allTokens|
                    && token == allTokens[i]
          invariant forall t <- allTokens[0..i] :: s.Contains(t.val)
        {
          if(token.Next == null) {
            firstToken.TokenNextIsNullImpliesLastToken(token, i);
          } else {
            firstToken.TokenNextIsIPlus1(token, i);
          }
          IsAllocated(allTokens[0..i]);
          var indentationBefore, indentationBeforeSet,
              lastIndentation, lastIndentationSet,
              indentationAfter, indentationAfterSet := reindent.GetIndentation(token, currentIndent);

          var newLeadingTrivia := reindent.Reindent(token, false, leadingTriviaWasPreceededByNewline, indentationBefore, lastIndentation);
          var newTrailingTrivia := reindent.Reindent(token, true, false, indentationAfter, indentationAfter);
          leadingTriviaWasPreceededByNewline := HelperString.FinishesByNewline(token.TrailingTrivia);
          ghost var sPrev := s;
          s := String.Concat(s, String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)));
          currentIndent := indentationAfter;
          ContainsTransitive();
          assert {:split_here} forall t <- allTokens[0..i+1] :: s.Contains(t.val);
          token := token.Next;
          i := i + 1;
        }
      }
    }
  }
}
