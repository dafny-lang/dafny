using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Linq;

namespace Microsoft.Dafny;

class AuditCommand : ICommandSpec {
  public IEnumerable<IOptionSpec> Options => new IOptionSpec[] {
    ReportFileOption.Instance,
    ReportFormatOption.Instance,
    CompareReportOption.Instance
  }.Concat(ICommandSpec.CommonOptions);

  public Command Create() {
    var result = new Command("audit", "Audit the program, optionally creating a report document.");
    result.AddArgument(ICommandSpec.FilesArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Options options, InvocationContext context) {
    dafnyOptions.Compile = false;
    dafnyOptions.Verify = false;
  }
}
