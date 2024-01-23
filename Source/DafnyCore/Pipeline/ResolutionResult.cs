#nullable enable
using System.Collections.Generic;

namespace Microsoft.Dafny;

public record ResolutionResult(
  bool HasErrors,
  Program ResolvedProgram,
  IReadOnlyList<ICanVerify>? CanVerifies);
