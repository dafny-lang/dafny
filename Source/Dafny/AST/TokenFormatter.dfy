module {:extern @" Helpers {
  public class HelperString {
    public static readonly System.Text.RegularExpressions.Regex NewlineRegex =
      new System.Text.RegularExpressions.Regex(new string(new char[]  
        {'(','?','m',')','^','\\','s','*'}));

    public static string Reindent(string input, string newIndent) {
      return NewlineRegex.Replace(input, newIndent);
    }
  }
} /*/"} DefaultCode {

}
module {:extern "/*/dummy{}", "Top"} {:compile false} {:options "-functionSyntax:4"} Top {
  type {:extern "*/string"} {:compile false} CsString(!new,0) {
    // TODO: need a better way to express infix operators.
    function {:extern "Substring(0)+"} {:compile false} concat(other: CsString): CsString
  }
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

      newtype {:native} CInt = x: int | 0 <= x < 65535


      function {:extern} {:macro "new string(character, length)"} newString(character: char, length: CInt): CsString
      const {:extern @"""", @"Substring(0)"} CsStringEmpty: CsString;

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
          s := s.concat(token.leadingTrivia).concat(token.val).concat(token.trailingTrivia);
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
          s := s.concat(leadingTrivia).concat(token.val).concat(trailingTrivia);
          token := token.next;
        }
      }
    }
  }
}