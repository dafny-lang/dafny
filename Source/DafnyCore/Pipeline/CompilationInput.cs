using System;
using OmniSharp.Extensions.LanguageServer.Protocol;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny {
  /// <summary>
  /// Contains all the inputs of a Compilation
  /// </summary>
  public record CompilationInput(DafnyOptions Options, int Version, DafnyProject Project) {

    public override string ToString() {
      return $"URI: {Uri}, Version: {Version}";
    }
    public DocumentUri Uri => Project.Uri;
  }

  public record BufferLine(int LineNumber, int StartIndex, int EndIndex);
}
