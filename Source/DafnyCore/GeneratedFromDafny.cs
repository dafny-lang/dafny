/// Microsoft.Dafny.Formatting.__default.ReindentProgramFromFirstToken() takes
/// - A first token, from which an entire program is available
/// - An IIndentationFormatter, that knows how to indent every token
/// It then prints every token (proven separatedly) in order, reindenting its leading trivia and trailing trivia

using System;
using System.Numerics;
using System.Collections;
using Microsoft.Dafny;

namespace Formatting {

  public interface IIndentationFormatter {
    String GetNewLeadingTrivia(IToken token);
    String GetNewTrailingTrivia(IToken token);
    void GetNewLeadingTrailingTrivia(IToken token, out String newLeadingTrivia, out String newTrailingTrivia);
  }
  public class _Companion_IIndentationFormatter {
    public static void GetNewLeadingTrailingTrivia(
        IIndentationFormatter _this, IToken token,
        out String newLeadingTrivia, out String newTrailingTrivia) {
      newLeadingTrivia = _this.GetNewLeadingTrivia(token);
      newTrailingTrivia = _this.GetNewTrailingTrivia(token);
    }
  }

  public partial class __default {
    public static String ReindentProgramFromFirstToken(IToken firstToken, IIndentationFormatter reindent) {
      String s = "";
      IToken token = firstToken;
      StringBuilder sb = new StringBuilder();
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



