module {:extern @" Helpers {
  public class HelperString {
    public static readonly System.Text.RegularExpressions.Regex NewlineRegex =
      new System.Text.RegularExpressions.Regex(new string(new char[]  
        {'(','?','m',')','(','^',')','\\','s','*'}));

    public static string Reindent(string input, string newIndent) {
      return NewlineRegex.Replace(input, newIndent);
    }
  }
} /*/"} DefaultCode {
}
module {:extern "System"} {:compile false} {:options "-functionSyntax:4"} System {
  type {:extern "String"} CsString(!new)
  class {:extern "String"} {:compile false} String {
    static function Concat(s1: CsString, s2: CsString): CsString
  }
}
module {:extern "/*/dummy{}", "Top"} {:compile false} {:options "-functionSyntax:4"} Top {
  import opened System
  trait {:extern "*/Microsoft.Dafny.IToken"} {:compile false} IToken {
    var val: CsString
    var leadingTrivia: CsString
    var trailingTrivia: CsString
    ghost var remainingTokens: seq<IToken>
    var next: IToken?

    ghost predicate Valid() reads * decreases |remainingTokens| {
      if next == null then
        remainingTokens == []
      else
        && |remainingTokens| > 0
        && next == remainingTokens[0]
        && next.remainingTokens == remainingTokens[1..]
        && next.Valid()
    }
  }
}
module {:extern "Microsoft"} {:options "-functionSyntax:4"}  Microsoft {
  module {:extern "Dafny"} Dafny {
    module {:extern "TokenFormatter"} TokenFormatter {
      import opened Top
      import opened System

      newtype {:native} CInt = x: int | 0 <= x < 65535


      function {:extern} {:macro "new string(character, length)"} newString(character: char, length: CInt): CsString
      const {:extern "System", "String.Empty"} CsStringEmpty: CsString;

      function {:extern "Helpers.HelperString", "Reindent"} {:macro} Reindent(input: CsString, newIndent: CsString): (output: CsString)

      trait ITokenIndentations {
        // Returns -1 if no indentation is set
        method getIndentation(token: IToken) returns (indentation: CsString, wasSet: bool)
      }
      
      

      /** Prints the entire program without change */
      method printSource(firstToken: IToken) returns (s: CsString)
        requires firstToken.Valid()
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        while(token != null)
        decreases if token == null then 0 else |token.remainingTokens| + 1
        invariant token == null || token.Valid()
        {
          s := String.Concat(String.Concat(String.Concat(s, token.leadingTrivia), token.val), token.trailingTrivia);
          token := token.next;
        }
      }

      /** Prints the entire program while fixing identation, based on a map */
      method printSourceReindent(firstToken: IToken, reindent: ITokenIndentations) returns (s: CsString)
        requires firstToken.Valid()
      {
        var token: IToken? := firstToken;
        s := CsStringEmpty;
        var currentIndent := CsStringEmpty;
        var isSet := false;
        while(token != null)
        decreases if token == null then 0 else |token.remainingTokens| + 1
        invariant token == null || token.Valid()
        {
          var newIndent, wasSet := reindent.getIndentation(token);
          if(wasSet) {
            currentIndent := newIndent;
            isSet := true;
          }
          var leadingTrivia := if isSet then Reindent(token.leadingTrivia, currentIndent) else token.leadingTrivia;
          var trailingTrivia :=  if isSet then Reindent(token.trailingTrivia, newIndent) else token.trailingTrivia;
          s := String.Concat(String.Concat(String.Concat(s, leadingTrivia), token.val), trailingTrivia);
          token := token.next;
        }
      }
    }
  }
}