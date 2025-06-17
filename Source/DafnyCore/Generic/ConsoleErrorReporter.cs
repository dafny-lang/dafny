namespace Microsoft.Dafny;

public class ConsoleErrorReporter(DafnyOptions options) : BatchErrorReporter(options) {

  public override bool MessageCore(DafnyDiagnostic diagnostic) {
    var printMessage = base.MessageCore(diagnostic) && (Options is { PrintTooltips: true } || diagnostic.Level != ErrorLevel.Info);
    if (!printMessage) {
      return false;
    }

    Options.OutputWriter.WriteDiagnostic(diagnostic);

    return true;
  }
}