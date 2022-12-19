using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class AuditCommand : ICommandSpec {

  public IEnumerable<Option> Options => new Option[] {
    Auditor.Auditor.ReportFileOption,
    Auditor.Auditor.ReportFormatOption,
    Auditor.Auditor.CompareReportOption
  }.Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("audit", "Identify all assumptions in the program, emitting them as warnings or in a report document.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.Verify = false;
    dafnyOptions.AuditProgram = true;
  }
}
