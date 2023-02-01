using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  static class CaptureStateExtensions {

    public static void AddCaptureState(this BoogieStmtListBuilder builder, Statement statement) {
      if (DafnyOptions.O.ModelViewFile != null || DafnyOptions.O.TestGenOptions.WarnDeadCode) {
        builder.Add(CaptureState(statement));
      }
    }

    private static Bpl.Cmd CaptureState(Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(stmt.RangeToken.EndToken, true, null);
    }

    public static void AddCaptureState(this BoogieStmtListBuilder builder, IToken tok, bool isEndToken, string /*?*/ additionalInfo) {
      if (DafnyOptions.O.ModelViewFile != null || DafnyOptions.O.TestGenOptions.WarnDeadCode) {
        builder.Add(CaptureState(tok, isEndToken, additionalInfo));
      }
    }

    private static Bpl.Cmd CaptureState(IToken tok, bool isEndToken, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      var col = tok.col + (isEndToken ? tok.val.Length : 0);
      string description = $"{ErrorReporter.TokenToString(tok)}{(additionalInfo == null ? "" : (": " + additionalInfo))}";
      Bpl.QKeyValue kv = new Bpl.QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return Translator.TrAssumeCmd(tok, Bpl.Expr.True, kv);
    }
  }
}