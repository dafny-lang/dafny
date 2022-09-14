module {:extern @"Microsoft.Dafny.Helpers"} {:options "-functionSyntax:4"} Helpers {
  import opened System
  import opened MicrosoftDafny
  class {:extern "HelperString"} {:compile false} HelperString {
    static predicate FinishesByNewline(input: CsString)
  }
}
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  type {:extern "Int32"} Int32(!new,==)

  ghost function {:extern} GEq(left: Int32, right: Int32): (b: bool)
    ensures left == right ==> b
  type {:extern "String"} CsString(!new,==) {
    function Length(): Int32
    ghost function StringRep(): string
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
      ensures GEq(r.Length(), s1.Length())
      ensures GEq(r.Length(), s2.Length())
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
    ghost var remainingTokens: nat
    var Next: IToken?
    
    ghost predicate Valid() reads * decreases remainingTokens {
      if Next == null then
        remainingTokens == 0
      else
        && remainingTokens > 0
        && Next.remainingTokens == remainingTokens - 1
        && Next.Valid()
    }
    ghost function AllTokens(): (r: seq<IToken>) reads *
      requires Valid()
      ensures forall tok <- r :: tok.Valid()
      //ensures allocated(r)
      decreases remainingTokens
    {
      if Next == null then [this] else
        [this] + this.Next.AllTokens()
    }
    lemma AlltokenSpec(i: int)
      requires Valid()
      decreases remainingTokens
      requires 0 <= i < |this.AllTokens()|
      ensures this.AllTokens() == this.AllTokens()[..i] + this.AllTokens()[i].AllTokens()
    {
      if Next == null {
      } else if i == 0 {
      } else {
        this.Next.AlltokenSpec(i - 1);
      }
    }
    lemma TokenNextIsIPlus1(middle: IToken, i: int)
      requires Valid()
      requires 0 <= i < |AllTokens()|
      requires AllTokens()[i] == middle;
      requires middle.Next != null
      ensures 0 <= i + 1 < |AllTokens()| && AllTokens()[i+1] == middle.Next
    {
      if Next == null || i == 0 {
      } else {
        this.Next.TokenNextIsIPlus1(middle, i - 1);
      }
    }

    lemma TokenNextIsNullImpliesLastToken(middle: IToken, i: int)
      requires middle.Valid() && this.Valid()
      requires 0 <= i < |AllTokens()|
      requires middle == AllTokens()[i]
      requires middle.Next == null
      ensures i == |AllTokens()|-1
    {
      if Next == null {
      } else {
        assert Next.AllTokens() == AllTokens()[1..];
        Next.TokenNextIsNullImpliesLastToken(middle, i-1);
      }
    }
  }
}
module {:extern "Microsoft"} {:options "-functionSyntax:4"}  Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "Formatting"} Formatting {
      import opened MicrosoftDafny
      import opened System
      import opened Helpers
      
      const {:extern "System", "String.Empty"} CsStringEmpty: CsString;
      
      trait IIndentationFormatter {
        function Reindent(token: IToken, trailingTrivia: bool, precededByNewline: bool, indentation: CsString, lastIndentation: CsString): CsString
        // Returns -1 if no indentation is set
        method GetIndentation(token: IToken, currentIndentation: CsString)
          returns (
            indentationBefore: CsString,
            indentationBeforeSet: bool,
            lastIndentation: CsString,
            lastIndentationSet: bool,
            indentationAfter: CsString,
            indentationAfterSet: bool)
          requires token.Valid()
          ensures token.AllTokens() == old(token.AllTokens())
      }
      
      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {
      }

      /** Prints the entire program while fixing identation, based on a map */
      method printSourceReindent(firstToken: IToken, reindent: IIndentationFormatter) returns (s: CsString)
        requires firstToken.Valid()
        ensures forall token <- firstToken.AllTokens() :: s.Contains(token.val)
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        var currentIndent := CsStringEmpty;
        ghost var i := 0;
        var leadingTriviaWasPreceededByNewline := true;
        var allTokens := firstToken.AllTokens();
        while(token != null)
          decreases if token == null then 0 else token.remainingTokens + 1
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
