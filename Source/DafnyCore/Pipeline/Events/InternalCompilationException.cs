
using System;

namespace Microsoft.Dafny;

public record InternalCompilationException(MessageSource Source, Exception Exception) : ICompilationEvent {
}