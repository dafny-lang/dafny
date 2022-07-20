namespace Microsoft.Dafny.LanguageServer {
  public static class DafnyRequestNames {

    // Notifications from server to client
    public const string CompilationStatus = "dafny/compilation/status";
    public const string GhostDiagnostics = "dafny/ghost/diagnostics";
    public const string VerificationStatusGutter = "dafny/verification/status/gutter";
    public const string VerificationSymbolStatus = "dafny/textDocument/symbolStatus";

    // Requests from client to server
    public const string CounterExample = "dafny/counterExample";
    public const string VerifySymbol = "dafny/textDocument/verifySymbol";
    public const string CancelVerifySymbol = "dafny/textDocument/cancelVerifySymbol";
  }
}
