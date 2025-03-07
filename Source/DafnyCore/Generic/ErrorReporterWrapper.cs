#nullable enable
namespace Microsoft.Dafny;

public class ErrorReporterWrapper(ErrorReporter reporter, string msgPrefix) : BatchErrorReporter(reporter.Options) {
  public readonly ErrorReporter WrappedReporter = reporter;

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