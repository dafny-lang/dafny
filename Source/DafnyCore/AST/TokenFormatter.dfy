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
    const val : CsString
    const LeadingTrivia: CsString
    const TrailingTrivia: CsString
    ghost const remainingTokens: nat
    const Next: IToken?
    
    ghost predicate Valid() decreases remainingTokens {
      if Next == null then
        remainingTokens == 0
      else
        && remainingTokens > 0
        && Next.remainingTokens == remainingTokens - 1
        && Next.Valid()
    }
    lemma NextHasRemainingTokens()
      requires Valid()
      ensures Next != null ==> AllTokens().Drop(1) == Next.AllTokens();
    {
      if Next != null {
        assert AllTokens().Drop(1) == Next.AllTokens();
      }
    }
    ghost function AllTokens(): (r: List<IToken>) reads *
      requires Valid()
      ensures r.TokenCons?
      ensures r.Forall((tok: IToken) => tok.Valid())
      //ensures allocated(r)
      decreases remainingTokens
    {
      if Next == null then TokenCons(this, TokenNil) else
        TokenCons(this, this.Next.AllTokens())
    }
    /*lemma AlltokenSpec(i: int)
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
    }*/
    /*lemma TokenSuccessive(middle: IToken, i: int)
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
    }*/
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
      
      datatype StringEdit = StringEdit(start: nat, end: nat, insert: string)
      
      ghost predicate {:opaque} IsScript(x: seq<StringEdit>, sLength: nat) {
        if x == [] then true
        else
          var last := x[|x|-1];
          0 <= last.start <= last.end <= sLength &&
          if |x| == 1 then true
          else x[|x|-2].end < last.start && IsScript(x[..|x|-1], last.start)
      }
      ghost predicate {:opaque} IsScriptForward(x: seq<StringEdit>, sLength: nat) {
        if x == [] then true
        else
          var first := x[0];
          0 <= first.start <= first.end <= sLength &&
          if |x| == 1 then true
          else first.end < x[1].start && IsScriptForward(x[1..], sLength)
      }
      /* lemma IsScriptEqualsIsScriptForward_Step0(x: seq<StringEdit>, sLength: nat, i: nat)
         requires i < |x|
         requires IsScript(x, sLength)
         ensures var first := x[i];
           0 <= first.start <= first.end <= sLength
           && (i + 1 < |x| ==> first.end < x[i+1].start)
       {
         if x == [] {
         } else {
           var last := x[|x|-1];
           if |x| == 1 {
           } else {
             if i == |x| - 1 {
             } else {
               assert IsScript(x[..|x|-1], last.start);
               IsScriptEqualsIsScriptForward_Step0(x[..|x|-1], last.start, i);
             }
           }
         }
       }
       lemma IsScriptEqualsIsScriptForward_Step1(x: seq<StringEdit>, sLength: nat, i: nat)
         decreases |x|
         requires i < |x|
         requires IsScript(x, sLength)
         ensures IsScriptForward(x[i..], sLength)
       {
         if x == [] {
         } else {
           var last := x[|x|-1];
           if |x| == 1 {
           } else {
             if i == |x| - 1 {
             } else {
               assert IsScript(x[..|x|-1], last.start);
               IsScriptEqualsIsScriptForward_Step0(x, sLength, 0);
               IsScriptEqualsIsScriptForward_Step0(x[..|x|-1], last.start, i);
               var first := x[i];
               assert 0 <= first.start <= first.end <= sLength;
               assert first.end < x[i + 1].start;
               
               IsScriptEqualsIsScriptForward_Step1(x[i..], sLength, 0);
               
               assert IsScriptForward(x[i..], sLength);
             }
           }
         }
       }*/
      
      lemma lastStep(x: seq<StringEdit>, sLength: nat)
        requires |x| > 0
        requires var last := x[|x|-1];
          && 0 <= last.start <= last.end <= sLength
          && (|x| > 1 ==> x[|x|-2].end <= last.start )
          && IsScriptForward(x[..|x|-1], last.start);
        ensures
          IsScriptForward(x, sLength)
      {
        reveal IsScriptForward();
        var last := x[|x|-1];
        var first := x[0];
        if |x| == 1 {
          assert last == first;
          assert 0 <= first.start <= first.end <= sLength;
          assert IsScriptForward(x, sLength);
        } else {
          assert 0 <= first.start <= first.end <= sLength;
          assert first.end < x[1].start;
          assert IsScriptForward(x[1..], sLength);
          assert IsScriptForward(x, sLength);
        }
        
      }
      
      lemma IsScriptEqualsIsScriptForward(x: seq<StringEdit>, sLength: nat)
        requires IsScript(x, sLength)
        ensures IsScriptForward(x, sLength)
      {
        if x == [] {
          reveal IsScript(), IsScriptForward();
        } else {
          var last := x[|x|-1];
          var first := x[0];
          if |x| == 1 {
            reveal IsScript(), IsScriptForward();
          } else {
            assert x[|x|-2].end < last.start && IsScript(x[..|x|-1], last.start) by {
              reveal IsScript();
            }
            assert 0 <= first.start <= first.end <= sLength by {
              reveal IsScript(), IsScriptForward();
            }
            IsScriptEqualsIsScriptForward(x[..|x|-1], last.start);
            assert IsScriptForward(x[..|x|-1], last.start);
            lastStep(x, sLength);
            assert IsScriptForward(x, sLength);
          }
        }
      }
      
      
      lemma IsScriptAcceptsLongerStrings(x: seq<StringEdit>, sLength1: nat, sLength2: nat)
        requires sLength1 <= sLength2
        requires IsScript(x, sLength1)
        ensures IsScript(x, sLength2)
      {
      }

      lemma IsAllocated<T>(x: T)
        ensures allocated(x) {

      }
      
      function apply(s: string, edits: seq<StringEdit>): string
        decreases |edits|
        requires IsScript(edits, |s|)
      {
        if |edits| == 0 then
          s
        else
          var last := edits[|edits|-1];
          assert last.start <= |s[0..last.start] + last.insert + s[last.end..]|;
          assert IsScript(edits[..|edits|-1], last.start);
          IsScriptAcceptsLongerStrings(edits[..|edits|-1], last.start, |s[0..last.start] + last.insert + s[last.end..]|);
          apply(s[0..last.start] + last.insert + s[last.end..], edits[..|edits|-1])
      }
      
      function applyForward(s: string, edits: seq<StringEdit>, start: nat := 0, acc: string := ""): string
        decreases |edits|
        requires start <= |s|
        requires |edits| > 0 ==> start <= edits[0].start
        requires IsScriptForward(edits, |s|)
      {
        if |edits| == 0 then
          acc + s[start..]
        else
          var first := edits[0];
          reveal IsScriptForward();
          applyForward(s, edits[1..], first.end, acc + s[start..first.start] + first.insert)
      } by method {
        var tmp := acc;
        var offset: nat := start;
        var i: nat := 0;
        assert IsScriptForward(edits[..0], |s|) by {
          reveal IsScriptForward();
        }
        assert tmp + s[offset..] == applyForward(s, edits[..i], start, acc);
        while i < |edits|
          decreases |edits| - i
          invariant i <= |edits|
          invariant 0 <= offset <= |s|
          invariant i < |edits| ==> offset <= edits[i].start
          invariant IsScriptForward(edits[..i], |s|)
          invariant tmp + s[offset..] == applyForward(s, edits[..i], start, acc)
        {
          reveal IsScriptForward();
          var edit := edits[i];
          tmp := tmp + s[offset..edit.start] + edit.insert;
          offset := edit.end;
          i := i + 1;
        }
        assert i == |edits|;
        tmp := tmp + s[offset..];
        assert tmp == applyForward(s, edits[..|edits|], start, acc);
        assert edits == edits[..|edits|];
        assert tmp == applyForward(s, edits, start, acc);
        return tmp;
      }
      
      /** Prints the entire program while fixing identation, based on a map */
      method printSourceReindent(firstToken: IToken, reindent: ITokenIndentations) returns (s: CsString)
        requires firstToken.Valid()
        ensures firstToken.AllTokens().Forall((token: IToken) => s.Contains(token.val))
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
          invariant 0 <= i <= firstToken.AllTokens().Length()
          invariant if token != null
            then && token.AllTokens() == firstToken.AllTokens().Drop(i)
                 && i < firstToken.AllTokens().Length()
                 && token == firstToken.AllTokens().ElementAt(i)
            else i == firstToken.AllTokens().Length()
          invariant GEq(s.Length(), sLengthPrev) // Prove that the length increases
          invariant firstToken.AllTokens().Take(i).Forall((t: IToken) => s.Contains(t.val))
        {
          sLengthPrev := s.Length();
          var indentationBefore, indentationBeforeSet,
              lastIndentation, lastIndentationSet,
              indentationAfter, indentationAfterSet := reindent.GetIndentation(token, currentIndent);
          //assert forall t <- firstTokensUntilI ::t.val == old@a(t.val);
          var newLeadingTrivia := reindent.Reindent(token, false, leadingTriviaWasPreceededByNewline, indentationBefore, lastIndentation);
          var newTrailingTrivia := reindent.Reindent(token, true, false, indentationAfter, indentationAfter);
          leadingTriviaWasPreceededByNewline := HelperString.FinishesByNewline(token.TrailingTrivia);
          // Had an error here: caught by an invariant
          //s := String.Concat(newTrivia, token.val);
          assert firstToken.AllTokens().Take(i).Forall((t: IToken) => s.Contains(t.val));

          ghost var sBefore := s;
          s := String.Concat(s, String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)));
          currentIndent := indentationAfter;
          assert String.Concat(token.val, newTrailingTrivia).Contains(token.val);
          String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia))
            .ContainsTransitive(String.Concat(token.val, newTrailingTrivia), token.val);
          s.ContainsTransitive(String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)), token.val);
          assert String.Concat(newLeadingTrivia, String.Concat(token.val, newTrailingTrivia)).Contains(token.val);
          assert s.Contains(token.val);
          assert GEq(s.Length(), sLengthPrev);

          var prevToken := token;
          if token.Next != null {
            assert token.AllTokens().Drop(1) == token.Next.AllTokens();
            firstToken.AllTokens().DropIsAdditive(i, 1);
            assert token.Next.AllTokens() == firstToken.AllTokens().Drop(i + 1);
            assert token.Next.AllTokens().ElementAt(0) == token.Next;
            firstToken.AllTokens().DropElementAtAdditive(i+1, 0);
            assert firstToken.AllTokens().Drop(i + 1).ElementAt(0) == firstToken.AllTokens().ElementAt(i + 1);
            // == firstToken.AllTokens().Drop(i + 1);
            assert token.Next == firstToken.AllTokens().ElementAt(i + 1);
          } else {
            assert token.AllTokens() == firstToken.AllTokens().Drop(i);
            assert token.AllTokens().Length() == 1;
            assert i + 1 == firstToken.AllTokens().Length();
          }
          assert firstToken.AllTokens().Take(i).Forall((t: IToken) => sBefore.Contains(t.val));
          assert firstToken.AllTokens().Take(i + 1).Forall((t: IToken) => s.Contains(t.val));

          assert GEq(s.Length(), sLengthPrev);
          assert firstToken.AllTokens().Take(i + 1).Forall((t: IToken) => s.Contains(t.val));
          token := token.Next;
          i := i + 1;
          if token != null {
            assert token.AllTokens() == firstToken.AllTokens().Drop(i);
            assert token == firstToken.AllTokens().ElementAt(i);
          } else {
            assert i == firstToken.AllTokens().Length();
          }
          assert GEq(s.Length(), sLengthPrev);
          assert firstToken.AllTokens().Take(i).Forall((t: IToken) => s.Contains(t.val));
        }
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
