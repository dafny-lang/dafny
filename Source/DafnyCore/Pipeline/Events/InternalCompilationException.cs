
using System;

namespace Microsoft.Dafny;

public record InternalCompilationException(IPhase Phase, Exception Exception) : ICompilationEvent {
}