// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny; 

static class CoverageReportCommand {

  static CoverageReportCommand() {
    ReportsArgument = new("reports", r => {
      return r.Tokens.Where(t => !string.IsNullOrEmpty(t.Value)).Select(t => new FileInfo(t.Value)).ToList();
    }, true, "directories with coverage reports to be merged");
  }

  // FilesArgument is intended for Dafny files, so CoverageReportCommand adds its own argument instead
  public static Argument<List<FileInfo>> ReportsArgument { get; }
  public static readonly Argument<string> OutDirArgument = new("outDir",
    @"directory in which to save the combined coverage report");

  public static Command Create() {
    var result = new Command("merge-coverage-reports",
      "Merge several previously generated coverage reports together.");
    result.AddArgument(OutDirArgument);
    result.AddArgument(ReportsArgument);

    DafnyCli.SetHandlerUsingDafnyOptionsContinuation(result, (options, _) => {
      var coverageReporter = new CoverageReporter(options);
      coverageReporter.Merge(options.Get(ReportsArgument).ConvertAll(fileInfo => fileInfo.FullName),
        options.Get(OutDirArgument));
      return Task.FromResult(0);
    });
    return result;
  }
}
