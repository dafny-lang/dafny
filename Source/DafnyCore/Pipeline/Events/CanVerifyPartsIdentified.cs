using System.Collections.Generic;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record CanVerifyPartsIdentified(ICanVerify CanVerify, IReadOnlyList<IVerificationTask> Parts) : ICompilationEvent {
}