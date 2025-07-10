#nullable enable
using System;
using System.Collections.Generic;
using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public record ResolutionResult(
  bool HasErrors,
  Program ResolvedProgram,
  IDictionary<Uri, IIntervalTree<DafnyPosition, ICanVerify>>? CanVerifies);
