using System;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Options for managing the documents.
  /// </summary>
  public class DocumentOptions {
    /// <summary>
    /// The IConfiguration section of the document options.
    /// </summary>
    public const string Section = "Documents";

    /// <summary>
    /// Gets or sets when the automatic verification should be applied.
    /// </summary>
    public AutoVerification Verify { get; set; } = AutoVerification.OnChange;

    static DocumentOptions() {
      DafnyOptions.Install(DafnyOptions.Create());
      DafnyOptions.O.ApplyDefaultOptions();
      DafnyOptions.O.PrintIncludesMode = DafnyOptions.IncludesModes.None;
      // ShowSnippets == true enable boogie assertion's token to contain the range of expressions, not their single token
      DafnyOptions.O.ShowSnippets = true;
    }

    public string ProverOptions =>
      string.Join(" ", DafnyOptions.O.ProverOptions) +
      " O:model_compress=false" + " O:model.completion=true" +
      " O:model_evaluator.completion=true";
  }
}
