// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace Formatting {

  public partial class __default {
    public static System.String ReindentProgramFromFirstToken(Microsoft.Dafny.Token firstToken, Formatting.IIndentationFormatter reindent)
    {
      System.String s = default(System.String);
      Microsoft.Dafny.Token _0_token;
      _0_token = firstToken;
      System.Text.StringBuilder _1_sb;
      System.Text.StringBuilder _nw0 = new System.Text.StringBuilder();
      _1_sb = _nw0;
      while ((_0_token) != (object) ((object)null)) {
        System.String _2_newLeadingTrivia;
        _2_newLeadingTrivia = (reindent).GetNewLeadingTrivia(_0_token);
        System.String _3_newTrailingTrivia;
        _3_newTrailingTrivia = (reindent).GetNewTrailingTrivia(_0_token);
        (_1_sb).Append(_2_newLeadingTrivia);
        (_1_sb).Append(_0_token.val);
        (_1_sb).Append(_3_newTrailingTrivia);
        _0_token = _0_token.Next;
      }
      System.String _out0;
      _out0 = (_1_sb).ToString().ToString();
      s = _out0;
      return s;
    }
  }

  public interface IIndentationFormatter {
    System.String GetNewLeadingTrivia(Microsoft.Dafny.Token token);
    System.String GetNewTrailingTrivia(Microsoft.Dafny.Token token);
  }
  public class _Companion_IIndentationFormatter {
  }
} // end of namespace Formatting