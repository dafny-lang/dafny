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
  class {:extern "HelperString"} {:compile false} HelperString {
    static predicate EndsWithNewline(input: CsString)
  }
}
module {:extern "Microsoft"} {:options "-functionSyntax:4"}  Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "Formatting"} Formatting {
      import opened MicrosoftDafny
      import opened System

      const {:extern "System", "String.Empty"} CsStringEmpty: CsString;

      trait IIndentationFormatter {

        // Given the current indentation at this point
        // returns the leading trivia but with its indentation corrected.
        function ReindentLeadingTrivia(token: IToken, precededByNewline: bool, indentation: CsString, lastIndentation: CsString): CsString

        // Given the current indentation at this point
        // returns the trailing trivia but with its indentation corrected.
        function ReindentTrailingTrivia(token: IToken, precededByNewline: bool, indentation: CsString, lastIndentation: CsString): CsString

        // Given a token and the current indentation, returns the expected indentation
        // on the line before the token and at the token's line (used only if it's the first token on the line)
        // and for the line after the token (used only it's not followed by a token on the same line)
        method GetIndentation(token: IToken, currentIndentation: CsString)
          returns (
            indentationBefore: CsString,
            lastIndentation: CsString,
            indentationAfter: CsString)
          requires token.Valid()
          ensures token.allTokens == old(token.allTokens)

        // Given a token (including leading and trailing trivia), the current indentation, and whether the last trivia
        // was ending with a newline, returns the two new leading and trailing trivia of the token,
        // the new current indentation and whether the last trailing trivia ended with a newline
        method GetNewLeadingTrailingTrivia(token: IToken, currentIndent: CsString, previousTrailingTriviaEndedWithNewline: bool)
          returns (newLeadingTrivia: CsString,
                   newTrailingTrivia: CsString,
                   newIndentation: CsString,
                   nextLeadingTriviaWillBePrecededByNewline: bool)
          requires token.Valid()
          ensures token.Valid()
          ensures token.allTokens == old(token.allTokens)
          ensures nextLeadingTriviaWillBePrecededByNewline == HelperString.EndsWithNewline(token.TrailingTrivia)
        {
          var indentationBefore,
              lastIndentation,
              indentationAfter := GetIndentation(token, currentIndent);
          newLeadingTrivia := ReindentLeadingTrivia(token, previousTrailingTriviaEndedWithNewline, indentationBefore, lastIndentation);
          newTrailingTrivia := ReindentTrailingTrivia(token, false, indentationAfter, indentationAfter);
          newIndentation := indentationAfter;
          nextLeadingTriviaWillBePrecededByNewline := HelperString.EndsWithNewline(token.TrailingTrivia);
        }
      }

      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {
      }

      /** Prints the entire program while fixing identation, based on
          1) indentation information provided by the IIndentationFormatter reindent
          2) Reindentation algorithm provided by the same reindent */
      method ReindentProgramFromFirstToken(firstToken: IToken, reindent: IIndentationFormatter) returns (s: CsString)
        requires firstToken.Valid()
        ensures forall token <- firstToken.allTokens :: s.Contains(token.val)
      {
        var token: IToken? := firstToken;
        var sb := new CsStringBuilder();
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
          invariant forall t <- allTokens[0..i] :: sb.built.Contains(t.val)
        {
          if(token.Next == null) {
            firstToken.TokenNextIsNullImpliesLastToken(token, i);
          } else {
            firstToken.TokenNextIsIPlus1(token, i);
          }
          IsAllocated(allTokens[0..i]);

          var newLeadingTrivia,
              newTrailingTrivia,
              newCurrentIndent,
              newEndedWithNewline :=
            reindent.GetNewLeadingTrailingTrivia(token, currentIndent, leadingTriviaWasPreceededByNewline);
          leadingTriviaWasPreceededByNewline := newEndedWithNewline;
          currentIndent := newCurrentIndent;
          ghost var sPrev := sb.built;
          sb.Append(newLeadingTrivia);
          sb.Append(token.val);
          sb.Append(newTrailingTrivia);
          ContainsTransitive();
          assert {:split_here} forall t <- allTokens[0..i+1] :: sb.built.Contains(t.val);
          token := token.Next;
          i := i + 1;
        }
        s := sb.ToString();
      }
    }
  }
}
