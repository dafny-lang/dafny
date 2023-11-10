
using System;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record InternalCompilationException(Exception Exception) : ICompilationEvent {
}