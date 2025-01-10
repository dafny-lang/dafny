using System.Collections.Generic;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public static class CaptureStateExtensions {

    public const string AfterLoopIterationsStateMarker = "after some loop iterations";

    internal static void AddCaptureState(this BoogieStmtListBuilder builder, Statement statement) {
      if (builder.Options.ExpectingModel || builder.Options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        builder.Add(CaptureState(builder.Options, statement));
      }
    }

    private static Bpl.Cmd CaptureState(DafnyOptions options, Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(options, stmt.Origin.EndToken, true, null);
    }

    internal static void AddCaptureState(this BoogieStmtListBuilder builder, IOrigin tok, bool isEndToken, string /*?*/ additionalInfo) {
      if (builder.Options.ExpectingModel || builder.Options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
        builder.Add(CaptureState(builder.Options, tok, isEndToken, additionalInfo));
      }
    }

    private static Bpl.Cmd CaptureState(DafnyOptions options, IOrigin tok, bool isEndToken, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      string description;
      if (options.TestGenOptions.Mode != TestGenerationOptions.Modes.None && tok.val != null && tok.val.StartsWith("#")) {
        description = $"{tok.TokenToString(options)}{(additionalInfo == null ? tok.val : (": " + additionalInfo))}";
      } else {
        description = $"{tok.TokenToString(options)}{(additionalInfo == null ? "" : (": " + additionalInfo))}";
      }
      Bpl.QKeyValue kv = new Bpl.QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return BoogieGenerator.TrAssumeCmd(tok, Bpl.Expr.True, kv);
    }
  }
}