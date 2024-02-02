#nullable enable
using System;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record BoogieException(ICanVerify CanVerify, IImplementationTask Task, Exception Exception) : ICompilationEvent;