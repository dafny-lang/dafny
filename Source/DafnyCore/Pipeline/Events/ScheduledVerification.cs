namespace Microsoft.Dafny;

public record ScheduledVerification(ICanVerify CanVerify) : ICompilationEvent {
}