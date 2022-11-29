using System;
using System.Collections.Generic;
using System.Linq;
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
      ShowSnippetsOption.Instance.Set(DafnyOptions.O, true);
    }
    public List<string> AugmentedProverOptions =>
      DafnyOptions.O.ProverOptions.Concat(new List<string>() {
        "O:model_compress=false", // Replaced by "O:model.compact=false" if z3's version is > 4.8.6
        // "O:model.completion=true", TODO: determine if this is really necessary
        "O:model_evaluator.completion=true"
      }).ToList();
  }
}
