using System;
using System.IO;
using DafnyCore;

namespace Microsoft.Dafny;

public class ConsoleErrorReporter : BatchErrorReporter {

  public override bool MessageCore(DafnyDiagnostic diagnostic) {
    var printMessage = base.MessageCore(diagnostic) && (Options is { PrintTooltips: true } || diagnostic.Level != ErrorLevel.Info);
    if (!printMessage) {
      return false;
    }

    Options.OutputWriter.WriteDiagnostic(diagnostic);

    return true;
  }

  public ConsoleErrorReporter(DafnyOptions options) : base(options) {
  }
}