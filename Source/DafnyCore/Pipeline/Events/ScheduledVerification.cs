namespace Microsoft.Dafny.LanguageServer.Workspace;

public record ScheduledVerification(ICanVerify CanVerify) : ICompilationEvent {
}