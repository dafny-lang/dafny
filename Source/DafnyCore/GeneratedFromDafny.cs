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
    void GetNewLeadingTrailingTrivia(Microsoft.Dafny.IToken token, out System.String newLeadingTrivia, out System.String newTrailingTrivia);
  }
  public class _Companion_IIndentationFormatter {
    public static void GetNewLeadingTrailingTrivia(Formatting.IIndentationFormatter _this, Microsoft.Dafny.IToken token, out System.String newLeadingTrivia, out System.String newTrailingTrivia) {
      newLeadingTrivia = default(System.String);
      newTrailingTrivia = default(System.String);
      newLeadingTrivia = (_this).GetNewLeadingTrivia(token);
      newTrailingTrivia = (_this).GetNewTrailingTrivia(token);
    }
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
        System.String newTrailingTrivia;
        System.String _out0;
        System.String _out1;
        (reindent).GetNewLeadingTrailingTrivia(token, out _out0, out _out1);
        newLeadingTrivia = _out0;
        newTrailingTrivia = _out1;
        (sb).Append(newLeadingTrivia);
        (sb).Append(token.val);
        (sb).Append(newTrailingTrivia);
        token = token.Next;
      }
      System.String _out2;
      _out2 = (sb).ToString().ToString();
      s = _out2;
      return s;
    }
  }
} // end of namespace Formatting



