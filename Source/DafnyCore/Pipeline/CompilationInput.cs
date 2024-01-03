using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny {
  /// <summary>
  /// Contains all the inputs of a Compilation
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
  }

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
