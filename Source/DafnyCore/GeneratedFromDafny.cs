/// Microsoft.Dafny.Formatting.__default.ReindentProgramFromFirstToken() takes
/// - A first token, from which an entire program is available
/// - An IIndentationFormatter, that knows how to indent every token
/// It then prints every token (proven separatedly) in order, reindenting its leading trivia and trailing trivia

using System;
using System.Numerics;
using System.Collections;
using System.Text;
using Microsoft.Dafny;

namespace Formatting {

  public interface IIndentationFormatter {
    string GetNewLeadingTrivia(IToken token);
    string GetNewTrailingTrivia(IToken token);
    void GetNewLeadingTrailingTrivia(IToken token, out string newLeadingTrivia, out string newTrailingTrivia);
  }
  public class _Companion_IIndentationFormatter {
    public static void GetNewLeadingTrailingTrivia(
        IIndentationFormatter _this, IToken token,
        out string newLeadingTrivia, out string newTrailingTrivia) {
      newLeadingTrivia = _this.GetNewLeadingTrivia(token);
      newTrailingTrivia = _this.GetNewTrailingTrivia(token);
    }
  }

  public class __default {
    public static String ReindentProgramFromFirstToken(IToken firstToken, IIndentationFormatter reindent) {
      var s = "";
      var token = firstToken;
      var sb = new StringBuilder();
      while (token != null) {
        reindent.GetNewLeadingTrailingTrivia(token, out var newLeadingTrivia, out var newTrailingTrivia);
        sb.Append(newLeadingTrivia);
        sb.Append(token.val);
        sb.Append(newTrailingTrivia);
        token = token.Next;
      }
      return sb.ToString();
    }
  }
} // end of namespace Formatting



