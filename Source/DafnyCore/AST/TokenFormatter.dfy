module {:extern @"Microsoft.Dafny.Helpers"} {:options "-functionSyntax:4"} Helpers {
  import opened System
  import opened MicrosoftDafny
  class {:extern "HelperString"} {:compile false} HelperString {
    static predicate FinishesByNewline(input: CsString)
  }
}
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  trait {:extern " Collections.Generic.IEnumerator"} {:compile false} IEnumerator<T> {
    method MoveNext() returns (r: bool)
    function Current(): T reads this
  }
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
  class {:extern "String"} {:compile false} String {
    static function Concat(s1: CsString, s2: CsString): (r: CsString)
      ensures GEq(r.Length(), s1.Length())
      ensures GEq(r.Length(), s2.Length())
      ensures r.Contains(s1)
      ensures r.Contains(s2)
  }
}
module {:compile false} {:options "-functionSyntax:4"} SpecShouldNotCompile {
  datatype List<T> = TokenCons(head: T, tail: List<T>) | TokenNil
  {
    ghost function Elements(): set<T> {
      if TokenCons? then {head} + tail.Elements() else {}
    }
    ghost function Length(): nat {
      if TokenCons? then 1 + tail.Length() else 0
    }
    ghost predicate Forall(p: T ~> bool)
      requires forall t <- Elements() :: p.requires(t) && p.reads(t) == {}
    {
      if TokenCons? then p(head) && tail.Forall(p) else true
    }
    ghost function ElementAt(i: nat): T
      requires i < Length()
    {
      if i == 0 then head else tail.ElementAt(i-1)
    }
    ghost function Take(i: nat): List<T>
      requires i <= Length()
    {
      if i == 0 then TokenNil else TokenCons(head, tail.Take(i-1))
    }
    ghost function Drop(i: nat): (result: List<T>)
      requires i <= Length()
      ensures result.Length() == Length() - i
    {
      if i == 0 then this else tail.Drop(i-1)
    }
    lemma DropIsAdditive(i: nat, j: nat)
      requires i + j < Length();
      ensures Drop(i).Drop(j) == Drop(i+j)
    {
    }
    lemma DropElementAtAdditive(i: nat, j: nat)
      requires i + j < Length()
      ensures Drop(i).ElementAt(j) == ElementAt(i + j)
    {

    }
  }
}
module {:extern "Microsoft.Dafny"} {:compile false} {:options "-functionSyntax:4"} MicrosoftDafny {
  import opened System
  import opened SpecShouldNotCompile

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
    lemma TokenSuccessive(middle: IToken, i: int)
      requires Valid()
      requires middle.Next != null
      requires 0 <= i < |AllTokens()|
      requires AllTokens()[i] == middle;
      ensures 0 <= i + 1 < |AllTokens()| && AllTokens()[i+1] == middle.Next
    {
      if Next == null || i == 0 {
      } else {
        this.Next.TokenSuccessive(middle, i - 1);
      }
    }
  }
}
module {:extern "Microsoft"} {:options "-functionSyntax:4"}  Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "TokenFormatter"} TokenFormatter {
      import opened MicrosoftDafny
      import opened System
      import opened Helpers
      
      newtype {:native} CInt = x: int | 0 <= x < 65535
      
      
      function {:extern} {:macro "new string(character, length)"} newString(character: char, length: CInt): CsString
      const {:extern "System", "String.Empty"} CsStringEmpty: CsString;
      
      trait ITokenIndentations {
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
          ensures unchanged(token)
          ensures token.AllTokens() == old(token.AllTokens())
      }
      
      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {

      }

      lemma TokenAtLast(token: IToken, firstToken: IToken, i: int)
        requires token.Valid() && firstToken.Valid()
        requires 0 <= i < |firstToken.AllTokens()|
        requires token == firstToken.AllTokens()[i]
        requires token.Next == null
        ensures i == |firstToken.AllTokens()|-1
      {
        if firstToken.Next == null {
        } else {
          assert firstToken.Next.AllTokens() == firstToken.AllTokens()[1..];
          TokenAtLast(token, firstToken.Next, i-1);
        }
      }

      lemma TokenNotAtLast(token: IToken, firstToken: IToken, i: int)
        requires token.Valid() && firstToken.Valid()
        requires 0 <= i < |firstToken.AllTokens()|
        requires token == firstToken.AllTokens()[i]
        requires token.Next != null
        ensures i < |firstToken.AllTokens()|-1
      {
        if firstToken.Next == null {
        } else if i == 0 {
        } else {
          assert firstToken.Next.AllTokens() == firstToken.AllTokens()[1..];
          TokenNotAtLast(token, firstToken.Next, i-1);
        }
      }
      
      /** Prints the entire program while fixing identation, based on a map */
      method printSourceReindent(firstToken: IToken, reindent: ITokenIndentations) returns (s: CsString)
        requires firstToken.Valid()
        ensures forall token <- firstToken.AllTokens() :: s.Contains(token.val)
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        var currentIndent := CsStringEmpty;
        var currentIndentLast := CsStringEmpty;
        var isSet := false;
        ghost var sLengthPrev := s.Length();
        ghost var i := 0;
        var leadingTriviaWasPreceededByNewline := true;
        while(token != null)
          decreases if token == null then 0 else token.remainingTokens + 1
          invariant token == null || token.Valid()
          invariant 0 <= i <= |firstToken.AllTokens()|
          invariant if token != null
            then && i < |firstToken.AllTokens()|
                 && token == firstToken.AllTokens()[i]
            else i == |firstToken.AllTokens()|
          invariant GEq(s.Length(), sLengthPrev);
          invariant forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val)
        {
          
          if(token.Next == null) {
            TokenAtLast(token, firstToken, i);
            assert i == |firstToken.AllTokens()|-1;
          }
          //assert if token.Next != null then i+1 < |firstToken.AllTokens()| else i + 1 == |firstToken.AllTokens()|;
          var firstTokensUntilI := firstToken.AllTokens()[0..i];
          assert forall t <- firstTokensUntilI :: s.Contains(t.val);
          sLengthPrev := s.Length();
          assert forall t <- firstTokensUntilI :: s.Contains(t.val);
          IsAllocated(firstTokensUntilI);
          assert allocated(firstTokensUntilI);
          var indentationBefore, indentationBeforeSet,
              lastIndentation, lastIndentationSet,
              indentationAfter, indentationAfterSet := reindent.GetIndentation(token, currentIndent);
          //assert forall t <- firstTokensUntilI ::t.val == old@a(t.val);
          assert forall t <- firstTokensUntilI :: s.Contains(t.val);
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);

          var newLeadingTrivia := reindent.Reindent(token, false, leadingTriviaWasPreceededByNewline, indentationBefore, lastIndentation);
          var newTrailingTrivia := reindent.Reindent(token, true, false, indentationAfter, indentationAfter);
          leadingTriviaWasPreceededByNewline := HelperString.FinishesByNewline(token.TrailingTrivia);
          // Had an error here: caught by an invariant
          //s := String.Concat(newTrivia, token.val);
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          ghost var sPrev := s;
          var tokenTrailing := String.Concat(token.val, newTrailingTrivia);
          var right := String.Concat(newLeadingTrivia, tokenTrailing);
          s := String.Concat(s, right);
          currentIndent := indentationAfter;
          assert String.Concat(token.val, newTrailingTrivia).Contains(token.val);
          String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia))
            .ContainsTransitive(String.Concat(token.val, newTrailingTrivia), token.val);
          s.ContainsTransitive(String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)), token.val);
          forall t <- firstToken.AllTokens()[0..i]
            ensures s.Contains(t.val)
          {
            assert sPrev.Contains(t.val);
            assert s.Contains(sPrev);
            s.ContainsTransitive(sPrev, t.val);
          }
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);

          assert String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)).Contains(token.val);
          assert allocated(firstToken.AllTokens()[0..i]);
          assert s.Contains(token.val);
          
          if(token.Next != null) {
            TokenNotAtLast(token, firstToken, i);
            assert {:split_here} i+1 < |firstToken.AllTokens()|;
            
            firstToken.AlltokenSpec(i + 1);
            assert token == firstToken.AllTokens()[i];
            firstToken.TokenSuccessive(token, i);
            assert token.Next == firstToken.AllTokens()[i + 1];
          }
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          assert s.Contains(firstToken.AllTokens()[i].val);
          assert forall t <- firstToken.AllTokens()[0..i + 1] :: s.Contains(t.val);
          var prevToken := token;
          var prevI := i;

          token := token.Next;
          i := i + 1;
          assert prevToken != null;
          assert prevI < |firstToken.AllTokens()|
                 && prevToken == firstToken.AllTokens()[prevI];
          assert prevToken == firstToken.AllTokens()[prevI];
          if(token == null) {
            assert i == |firstToken.AllTokens()|;
          }
          
          
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
        }
        assert  forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
        assert i == |firstToken.AllTokens()|;
        assert forall token <- firstToken.AllTokens() :: s.Contains(token.val);
      }
    }
  }
}
