using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Dynamic;
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
  public class Compilation {
    /// <summary>
    /// These do not have to be owned
    /// </summary>
    public IReadOnlyList<Uri> RootUris { get; }
    public int Version { get; }
    public DafnyProject Project { get; }
    public DocumentUri Uri => Project.Uri;

    public Compilation(int version, DafnyProject project, IReadOnlyList<Uri> rootUris) {
      this.RootUris = rootUris;
      Version = version;
      Project = project;
    }

    public virtual IEnumerable<DafnyDiagnostic> GetDiagnostics(Uri uri) => Enumerable.Empty<DafnyDiagnostic>();

    public IdeState InitialIdeState(Compilation initialCompilation, DafnyOptions options) {
      var program = new EmptyNode();
      return ToIdeState(new IdeState(initialCompilation.Version, initialCompilation, program,
        ImmutableDictionary<Uri, IReadOnlyList<Diagnostic>>.Empty,
        SymbolTable.Empty(), LegacySignatureAndCompletionTable.Empty(options, initialCompilation.Project), ImmutableDictionary<Uri, Dictionary<Range, IdeVerificationResult>>.Empty,
        Array.Empty<Counterexample>(),
        ImmutableDictionary<Uri, IReadOnlyList<Range>>.Empty,
        initialCompilation.RootUris.ToDictionary(uri => uri, uri => new DocumentVerificationTree(program, uri))
      ));
    }

    /// <summary>
    /// Collects information to present to the IDE
    /// </summary>
    public virtual IdeState ToIdeState(IdeState previousState) {
      return previousState with {
        Compilation = this
      };
    }
  }

  public record ImplementationView(IImplementationTask Task, PublishedVerificationStatus Status,
    IReadOnlyList<DafnyDiagnostic> Diagnostics);

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
