using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

static class AuditCommand {

  public static IEnumerable<Option> Options => new Option[] {
    Auditor.Auditor.ReportFileOption,
    Auditor.Auditor.ReportFormatOption,
    Auditor.Auditor.CompareReportOption
  }.Concat(DafnyCommands.ResolverOptions);

  public static Command Create() {
    var result = new Command("audit", "Report issues in the Dafny code that might limit the soundness claims of verification, emitting them as warnings or in a report document.");
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }

    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      options.Compile = false;
      options.Verify = false;
      options.AuditProgram = true;
      return CompilerDriver.RunCompiler(options);
    });
    return result;
  }
}
