using static Microsoft.Dafny.ResolutionErrors;

namespace Microsoft.Dafny;

partial class ModuleResolver {
  public void ReportWarning(ErrorId errorId, IOrigin t, string msg, params object[] args) {
    reporter.Warning(MessageSource.Resolver, errorId, t, msg, args);
  }

  public void ReportError(ErrorId errorId, IOrigin t, string msg, params object[] args) {
    reporter.Error(MessageSource.Resolver, errorId, t, msg, args);
  }

  public void ReportError(ErrorId errorId, INode t, string msg, params object[] args) {
    reporter.Error(MessageSource.Resolver, errorId, t, msg, args);
  }
}