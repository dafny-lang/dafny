using System;
using System.Collections.Immutable;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record FinishedParsing(
  Program Program,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics) : ICompilationEvent {
}