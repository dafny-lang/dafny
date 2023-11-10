using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Dynamic;
using System.Linq;
using Microsoft.Boogie;
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
    /// <summary>
    /// These do not have to be owned
    /// </summary>
    public IReadOnlyList<Uri> RootUris { get; }

    public override string ToString() {
      return $"URI: {Uri}, Version: {Version}";
    }

    public IEnumerable<Uri> RootAndProjectUris => RootUris.Concat(new[] { Project.Uri }).Distinct();
    public int Version { get; }
    public DafnyOptions Options { get; }
    public DafnyProject Project { get; }
    public DocumentUri Uri => Project.Uri;

    public CompilationInput(DafnyOptions options, int version, DafnyProject project, IReadOnlyList<Uri> rootUris) {
      RootUris = rootUris;
      Options = options;
      Version = version;
      Project = project;
    }
  }

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
