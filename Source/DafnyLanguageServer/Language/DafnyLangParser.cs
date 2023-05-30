using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser, IDisposable {
    private readonly DafnyOptions options;
    private readonly ILogger logger;
    private readonly SemaphoreSlim mutex = new(1);

    private DafnyLangParser(DafnyOptions options, ILogger<DafnyLangParser> logger) {
      this.options = options;
      this.logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    public static DafnyLangParser Create(DafnyOptions options, ILogger<DafnyLangParser> logger) {
      return new DafnyLangParser(options, logger);
    }

    public Dafny.Program CreateUnparsed(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);
      try {
        return NewDafnyProgram(document, errorReporter);
      }
      finally {
        mutex.Release();
      }
    }

    public Dafny.Program Parse(DocumentTextBuffer document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);

      try {
        return ParseUtils.ParseFiles(document.Uri.ToString(),
          new DafnyFile[]
          {
            new(errorReporter.Options, document.Uri.ToUri(), document.Content)
          },
          errorReporter, cancellationToken);
      }
      finally {
        mutex.Release();
      }
    }

    private Dafny.Program NewDafnyProgram(TextDocumentItem document, ErrorReporter errorReporter) {
      // Ensure that the statically kept scopes are empty when parsing a new document.
      Type.ResetScopes();
      return new Dafny.Program(
        document.Uri.ToString(),
        new LiteralModuleDecl(new DefaultModuleDefinition(new List<Uri>(), false), null),
        // BuiltIns cannot be initialized without Type.ResetScopes() before.
        new BuiltIns(errorReporter.Options),
        errorReporter, Sets.Empty<Uri>(), Sets.Empty<Uri>()
      );
    }

    public void Dispose() {
      mutex.Dispose();
    }
  }
}
