using System.Collections.Generic;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record ResolutionResult(
  Program ResolvedProgram,
  IReadOnlyList<ICanVerify>? CanVerifies);
