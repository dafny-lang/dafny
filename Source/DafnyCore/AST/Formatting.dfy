/// To compile this program, execute Source/DafnyCore/DafnyGeneratedFromDafny.sh manually for now

/// Microsoft.Dafny.Formatting.ReindentProgramFromFirstToken() takes
/// - A first token, from which an entire program is available
/// - A IIndentationFormatter, that knows how to indent every token
/// It then prints every token (proven) in order, reindenting its leading trivia and trailing trivia

include "System.dfy"
include "DafnyInterface.dfy"

// Provided new Dafny code (trait Microsoft.Dafny.Formatting.IIndentationFormatter)
@Options("-functionSyntax:4")
module {:extern "Microsoft"} Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "Formatting"} Formatting {
      import opened MicrosoftDafny
      import opened System

      const {:extern "System", "String.Empty"} CsStringEmpty: CsString

      trait IIndentationFormatter {
        // Given the current indentation at this point
        // returns the leading trivia but with its indentation corrected.
        function GetNewLeadingTrivia(token: Token): CsString

        // Given the current indentation at this point
        // returns the trailing trivia but with its indentation corrected.
        function GetNewTrailingTrivia(token: Token): CsString
      }

      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {
      }

      /** Prints the entire program while fixing indentation, based on
          1) indentation information provided by the IIndentationFormatter reindent
          2) Reindentation algorithm provided by the same reindent */
      method ReindentProgramFromFirstToken(firstToken: Token, reindent: IIndentationFormatter) returns (s: CsString)
        requires firstToken.Valid()
        ensures forall token: Token <- firstToken.allTokens :: s.Contains(token.val)
      {
        var token: Token? := firstToken;
        var sb := new CsStringBuilder();
        ghost var i := 0;
        var allTokens := firstToken.allTokens;
        while(token != null)
          decreases if token == null then 0 else |token.allTokens|
          invariant 0 <= i <= |allTokens|
          invariant if token == null then i == |allTokens| else
                    && token.Valid()
                    && i < |allTokens|
                    && token == allTokens[i]
          invariant forall t: Token <- allTokens[0..i] :: sb.built.Contains(t.val)
        {
          if(token.Next == null) {
            firstToken.TokenNextIsNullImpliesLastToken(token, i);
          } else {
            firstToken.TokenNextIsIPlus1(token, i);
          }
          IsAllocated(allTokens[0..i]);


          var newLeadingTrivia := reindent.GetNewLeadingTrivia(token);
          var newTrailingTrivia := reindent.GetNewTrailingTrivia(token);
          sb.Append(newLeadingTrivia);
          sb.Append(token.val);
          sb.Append(newTrailingTrivia);
          ContainsTransitive();
          assert {:split_here} forall t: Token <- allTokens[0..i+1] :: sb.built.Contains(t.val);
          token := token.Next;
          i := i + 1;
        }
        s := sb.ToString();
      }
    }
  }
}
