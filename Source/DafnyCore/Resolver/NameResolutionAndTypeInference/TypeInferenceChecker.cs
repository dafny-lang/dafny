using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny;

partial class ModuleResolver {
  public void ReportWarning(ErrorId errorId, IOrigin t, params object[] messageParts) {
    reporter.Warning(MessageSource.Resolver, errorId, t, messageParts);
  }

  public void ReportError(ErrorId errorId, IOrigin t, params object[] messageParts) {
    reporter.Error(MessageSource.Resolver, errorId, t, messageParts);
  }

  public void ReportError(ErrorId errorId, INode t, params object[] messageParts) {
    reporter.Error(MessageSource.Resolver, errorId, t, messageParts);
  }
}