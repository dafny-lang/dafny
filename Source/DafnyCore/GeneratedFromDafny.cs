// Dafny program Formatting.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
namespace Formatting {

  public interface IIndentationFormatter {
    System.String GetNewLeadingTrivia(Microsoft.Dafny.IToken token);
    System.String GetNewTrailingTrivia(Microsoft.Dafny.IToken token);
  }
  public class _Companion_IIndentationFormatter {
  }

  public partial class __default {
    public static System.String ReindentProgramFromFirstToken(Microsoft.Dafny.IToken firstToken, Formatting.IIndentationFormatter reindent) {
      System.String s = default(System.String);
      Microsoft.Dafny.IToken token;
      token = firstToken;
      System.Text.StringBuilder sb;
      System.Text.StringBuilder _nw0 = new System.Text.StringBuilder();
      sb = _nw0;
      while ((token) != (object)((Microsoft.Dafny.IToken)null)) {
        System.String newLeadingTrivia;
        newLeadingTrivia = (reindent).GetNewLeadingTrivia(token);
        System.String newTrailingTrivia;
        newTrailingTrivia = (reindent).GetNewTrailingTrivia(token);
        (sb).Append(newLeadingTrivia);
        (sb).Append(token.val);
        (sb).Append(newTrailingTrivia);
        token = token.Next;
      }
      System.String _out0;
      _out0 = (sb).ToString().ToString();
      s = _out0;
      return s;
    }
  }
} // end of namespace Formatting



