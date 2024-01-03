
using System;

namespace Microsoft.Dafny;

public record InternalCompilationException(Exception Exception) : ICompilationEvent {
}