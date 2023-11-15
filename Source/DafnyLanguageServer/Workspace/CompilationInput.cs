using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace {


  /// <summary>
  /// Internal representation of a specific version of a Dafny document.
  ///
  /// Only one instance should exist of a specific version.
  /// Asynchronous compilation tasks use this instance to synchronise on.
  ///
  /// When verification starts, no new instances of Compilation will be created for this version.
  /// There can be different verification threads that update the state of this object.
  /// </summary>
  public class CompilationInput {

    public override string ToString() {
      return $"URI: {Uri}, Version: {Version}";
    }


    public int Version { get; }
    public DafnyOptions Options { get; }
    public DafnyProject Project { get; }
    public DocumentUri Uri => Project.Uri;

    public CompilationInput(DafnyOptions options, int version, DafnyProject project) {
      Options = options;
      Version = version;
      Project = project;
    }

    public IdeState InitialIdeState(DafnyOptions options) {
      var program = new EmptyNode();
      return new IdeState(Version, ImmutableHashSet<Uri>.Empty,
        this, CompilationStatus.Parsing,
        program,
        ImmutableDictionary<Uri, ImmutableList<Diagnostic>>.Empty,
        program,
        SymbolTable.Empty(),
        LegacySignatureAndCompletionTable.Empty(options, Project), ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>>.Empty,
        Array.Empty<Counterexample>(),
        ImmutableDictionary<Uri, IReadOnlyList<Range>>.Empty,
        ImmutableDictionary<Uri, DocumentVerificationTree>.Empty
      );
    }
  }

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
