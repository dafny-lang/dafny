#nullable enable
using System.Linq;

namespace Microsoft.Dafny;

public class ErrorReporterWrapper(ErrorReporter reporter, DafnyRelatedInformation additionalRelatedInformation)
  : BatchErrorReporter(reporter.Options) {

  public readonly ErrorReporter WrappedReporter = reporter;

  public override bool MessageCore(DafnyDiagnostic dafnyDiagnostic) {
    if (dafnyDiagnostic.Level == ErrorLevel.Warning) {
      return false;
    }

    base.MessageCore(dafnyDiagnostic);
    return WrappedReporter.MessageCore(dafnyDiagnostic with {
      RelatedInformation = dafnyDiagnostic.RelatedInformation.Concat([additionalRelatedInformation]).ToList()
    });
  }
}