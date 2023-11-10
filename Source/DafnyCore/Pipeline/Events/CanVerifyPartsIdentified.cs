using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record CanVerifyPartsIdentified(ICanVerify CanVerify, IReadOnlyList<IImplementationTask> Parts) : ICompilationEvent {
}