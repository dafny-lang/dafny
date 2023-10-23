using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Plugins;

public interface IDafnyCodeActionInput {
  /// <summary>
  /// The URI of the document being considered
  /// </summary>
  string Uri { get; }
  Program? Program { get; }
  IEnumerable<DafnyDiagnostic> Diagnostics { get; }
  VerificationTree? VerificationTree { get; }
}