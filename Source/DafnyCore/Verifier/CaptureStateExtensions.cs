using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  static class CaptureStateExtensions {

    public static void AddCaptureState(this BoogieStmtListBuilder builder, Statement statement) {
      if (builder.Options.ModelViewFile != null || builder.Options.TestGenOptions.WarnDeadCode) {
        builder.Add(CaptureState(builder.Options, statement));
      }
    }

    private static Bpl.Cmd CaptureState(DafnyOptions options, Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(options, stmt.RangeToken.EndToken, true, null);
    }

    public static void AddCaptureState(this BoogieStmtListBuilder builder, IToken tok, bool isEndToken, string /*?*/ additionalInfo) {
      if (builder.Options.ModelViewFile != null || builder.Options.TestGenOptions.WarnDeadCode) {
        builder.Add(CaptureState(builder.Options, tok, isEndToken, additionalInfo));
      }
    }

    private static Bpl.Cmd CaptureState(DafnyOptions options, IToken tok, bool isEndToken, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      var col = tok.col + (isEndToken ? tok.val.Length : 0);
      string description = $"{tok.TokenToString(options)}{(additionalInfo == null ? "" : (": " + additionalInfo))}";
      Bpl.QKeyValue kv = new Bpl.QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return Translator.TrAssumeCmd(tok, Bpl.Expr.True, kv);
    }
  }
}