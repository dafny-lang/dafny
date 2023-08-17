// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public class CoverageReportCommand : ICommandSpec {

  static CoverageReportCommand() {
    ReportsArgument = new("reports", r => {
      return r.Tokens.Where(t => !string.IsNullOrEmpty(t.Value)).Select(t => new FileInfo(t.Value)).ToList();
    }, true, "directories with coverage reports to be merged");
  }

  // FilesArgument is intended for Dafny files, so CoverageReportCommand adds its own argument instead
  public static Argument<List<FileInfo>> ReportsArgument { get; }
  public static readonly Argument<string> OutDirArgument = new("outDir",
    @"directory in which to save the combined coverage report");

  public IEnumerable<Option> Options => new List<Option>();

  public Command Create() {
    var result = new Command("merge-coverage-reports",
      "Merge several previously generated coverage reports together.");
    result.AddArgument(OutDirArgument);
    result.AddArgument(ReportsArgument);
    return result;
  }

  public void PostProcess(DafnyOptions dafnyOptions, Microsoft.Dafny.Options options, InvocationContext context) { }
}
