#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record FinishedResolution(
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> Diagnostics,
  Program ResolvedProgram,
  IReadOnlyList<ICanVerify>? CanVerifies) : ICompilationEvent {

}