#nullable enable
namespace Microsoft.Dafny;

public class ErrorReporterWrapper : BatchErrorReporter {

  private string msgPrefix;
  public readonly ErrorReporter WrappedReporter;

  public ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : base(reporter.Options) {
    this.msgPrefix = msgPrefix;
    this.WrappedReporter = reporter;
  }

  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (dafnyDiagnostic.Level == ErrorLevel.Warning) {
      return false;
    }

    base.MessageCore(dafnyDiagnostic);
    return WrappedReporter.MessageCore(dafnyDiagnostic with {
      Message = msgPrefix + dafnyDiagnostic.Message
    });
  }
}