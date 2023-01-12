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

  }
}
