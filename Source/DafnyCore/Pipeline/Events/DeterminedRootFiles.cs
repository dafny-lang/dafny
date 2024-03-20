using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public record DeterminedRootFiles(
  DafnyProject Project,
  IReadOnlyList<DafnyFile> Roots,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics) : ICompilationEvent {
}