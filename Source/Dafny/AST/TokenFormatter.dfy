module {:extern @"Microsoft.Dafny.Helpers"} {:options "-functionSyntax:4"} Helpers {
  import opened System
  class {:extern "HelperString"} {:compile false} HelperString {
    static function Reindent(input: CsString, indentationBefore: CsString, lastIndentation: CsString): CsString
  }
}
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  trait {:extern " Collections.Generic.IEnumerator"} {:compile false} IEnumerator<T> {
    method MoveNext() returns (r: bool)
    function Current(): T reads this
  }
  type {:extern "Int32"} Int32(==)
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
module {:extern "Microsoft.Dafny"} {:compile false} {:options "-functionSyntax:4"} MicrosoftDafny {
  import opened System
  trait {:extern "IToken"} {:compile false} IToken {
    var val: CsString
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
    /*lemma AllTokensSuffix(token: IToken, i: int)
      requires Valid()
      requires 0 <= i < |this.AllTokens()|
      requires var token := this.AllTokens()[i];
               token.Next != null
      ensures i + 1 < |this.AllTokens()|
      ensures var token := this.AllTokens()[i];
              token.Next == this.AllTokens()[i + 1]
    {
      var token := this.AllTokens()[i];
      assert token.Next != null;
      if Next != null {
        //AllTokensSuffix(token.Next, i - 1);
        calc {
          this.AllTokens();
          [this] + this.Next.AllTokens();
        }
        assert i + 1 < |this.AllTokens()|;
        assert token.Next == this.AllTokens()[i + 1];
      } else {

      }
    }
    ghost function AllTokensUntil(other: IToken): seq<IToken> reads *
      requires Valid()
      decreases remainingTokens
      {
      if this == other then [] else
      if Next == null then [this] else
      [this] + this.Next.AllTokensUntil(other)
    }*/
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
        // Returns -1 if no indentation is set
        method GetIndentation(token: IToken, currentIndentation: CsString)
          returns (
            indentationBefore: CsString,
            lastIndentation: CsString,
            indentationAfter: CsString,
            wasSet: bool)
          requires token.Valid()
          ensures unchanged(token)
          ensures token.AllTokens() == old(token.AllTokens())
      }
      
      

      /** Prints the entire program without change */
      method printSource(firstToken: IToken) returns (s: CsString)
        requires firstToken.Valid()
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        while(token != null)
          decreases if token == null then 0 else token.remainingTokens + 1
          invariant token == null || token.Valid()
        {
          s := String.Concat(String.Concat(String.Concat(s, token.LeadingTrivia), token.val), token.TrailingTrivia);
          token := token.Next;
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
        var previousTrailingTrivia := CsStringEmpty;
        ghost var sLengthPrev := s.Length();
        ghost var i := 0;
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
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          sLengthPrev := s.Length();
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          // TODO: Dafny clinic
          var indentationBefore, lastIndentation, indentationAfter, wasSet := reindent.GetIndentation(token, currentIndent);
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          if(wasSet) {
            currentIndent := indentationBefore;
            currentIndentLast := lastIndentation;
            isSet := true;
          }
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          var triviaSoFar := String.Concat(previousTrailingTrivia, token.LeadingTrivia);
          var newTrivia := if isSet then
            HelperString.Reindent(triviaSoFar, indentationBefore, lastIndentation) else triviaSoFar;
          // Had an error here: caught by an invariant
          //s := String.Concat(newTrivia, token.val);
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          s := String.Concat(s, String.Concat(newTrivia, token.val));
          previousTrailingTrivia := token.TrailingTrivia;
          if(wasSet) {
            currentIndent := indentationAfter;
          }
          assert String.Concat(newTrivia, token.val).Contains(token.val);
          s.ContainsTransitive(String.Concat(newTrivia, token.val), token.val);
          assert s.Contains(token.val);
          
          if(token.Next != null) {
            assert {:split_here} i+1 < |firstToken.AllTokens()|;

            firstToken.AlltokenSpec(i + 1);
            assert token == firstToken.AllTokens()[i];
            firstToken.TokenSuccessive(token, i);
            assert token.Next == firstToken.AllTokens()[i + 1];
          }
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
          assert s.Contains(firstToken.AllTokens()[i].val);
          assert forall t <- firstToken.AllTokens()[0..i + 1] :: s.Contains(t.val);
          token := token.Next;
          i := i + 1;
          assert token != null ==> token == firstToken.AllTokens()[i];

          
          assert forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
        }
        s := String.Concat(s, previousTrailingTrivia);
        assert  forall t <- firstToken.AllTokens()[0..i] :: s.Contains(t.val);
        assert i == |firstToken.AllTokens()|;
        assert forall token <- firstToken.AllTokens() :: s.Contains(token.val);
      }

      datatype State = Indent(i: Int32)

      /** Design of a Domain-specific language to specify the pre-indentation and post-indentation of tokens */
      /*trait TokenTriviaStateMachine {
        var initState: State
        var currentState: State

        function transitionMap(state: State, str: CsString): State

        method Transition(token: IToken) modifies this`currentState {
          var newState := transitionMap(currentState, token.val);
          currentState := newState;
        }

        method SetBeforeAfter(token: IToken, before: Int32, after: Int32)

        method Walkthrough(tokens: IEnumerator<IToken>)
          decreases *
          modifies this`currentState
        {
          currentState := initState;
          while true
            decreases * {
            var hasNext := tokens.MoveNext();
            if(!hasNext) {
              break;
            }
            var currentToken := tokens.Current();
            Transition(currentToken);
          }
        }
      }*/
    }
  }
}