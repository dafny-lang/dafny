using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class CoverageInstrumenter {
  private readonly SinglePassCodeGenerator codeGenerator;
  private List<(IOrigin, string)>/*?*/ legend;  // non-null implies options.CoverageLegendFile is non-null
  private string talliesFilePath;

  public CoverageInstrumenter(SinglePassCodeGenerator codeGenerator) {
    this.codeGenerator = codeGenerator;
    if (codeGenerator.Options?.CoverageLegendFile != null
        || codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      legend = [];
    }

    if (codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      // Only a name is needed: the instrumented program opens this path with FileMode.Create
      // (see the CodeCoverage runtime emitted by CsharpCodeGenerator). Path.GetTempFileName()
      // would additionally create the file here, which then outlives the build whenever the
      // tallies are never read back -- on a target that rejects execution coverage, on a program
      // with no Main, and when the program fails before writing them.
      talliesFilePath = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    }
  }

  public bool IsRecording {
    get => legend != null;
  }

  public void Instrument(IOrigin tok, string description, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Record({0})", legend.Count);
      codeGenerator.EndStmt(wr);
      legend.Add((tok, description));
    }
  }

  public void UnusedInstrumentationPoint(IOrigin tok, string description) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    if (legend != null) {
      legend.Add((tok, description));
    }
  }

  public void InstrumentExpr(IOrigin tok, string description, bool resultValue, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      // The "Record" call always returns "true", so we negate it to get the value "false"
      wr.Write("{1}DafnyProfiling.CodeCoverage.Record({0})", legend.Count, resultValue ? "" : "!");
      legend.Add((tok, description));
    }
  }

  /// <summary>
  /// Should be called once "n" has reached its final value
  /// </summary>
  public void EmitSetup(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Setup({0}", legend.Count);
      if (talliesFilePath != null) {
        wr.Write($", @\"{talliesFilePath}\"");
      }
      wr.Write(")");
      codeGenerator.EndStmt(wr);
    }
  }

  public void EmitTearDown(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.TearDown()");
      codeGenerator.EndStmt(wr);
    }
  }

  public async Task WriteLegendFile() {
    if (codeGenerator.Options?.CoverageLegendFile == null) {
      return;
    }

    var filename = codeGenerator.Options.CoverageLegendFile;
    Contract.Assert(filename != null);
    await using TextWriter wr = filename == "-"
      ? codeGenerator.Options.OutputWriter.StatusWriter()
      : new StreamWriter(new FileStream(Path.GetFullPath(filename), FileMode.Create));
    for (var i = 0; i < legend.Count; i++) {
      var e = legend[i];
      await wr.WriteLineAsync($"{i}: {e.Item1.OriginToString(codeGenerator.Options)}: {e.Item2}");
    }

    legend = null;
  }

  public void PopulateCoverageReport(CoverageReport coverageReport) {
    var coverageReportDir = codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport);
    if (coverageReportDir != null) {
      try {
        PopulateFromTallies(coverageReport);
      }
      finally {
        // Delete even if the tallies could not be read: the program may have failed before writing
        // them, and on a target that rejects execution coverage they are never written at all.
        TryDeleteTalliesFile();
      }
    }
  }

  /// <summary>
  /// Best-effort removal of the tallies file. Never throws: this runs from a finally block, and
  /// leaving a file behind in the temp directory is not worth failing a build over, let alone
  /// masking the exception that sent us here.
  /// </summary>
  private void TryDeleteTalliesFile() {
    if (talliesFilePath == null) {
      return;
    }
    try {
      File.Delete(talliesFilePath);
    } catch (Exception) {
      // Includes IOException (file in use) and UnauthorizedAccessException (read-only or a
      // directory); nothing here is actionable.
    }
  }

  private void PopulateFromTallies(CoverageReport coverageReport) {
    // uint, matching the counters the instrumented program writes: a branch taken more than
    // int.MaxValue times would make int.Parse throw OverflowException.
    var tallies = File.ReadLines(talliesFilePath).Select(uint.Parse).ToArray();
    foreach (var ((token, _), tally) in legend.Zip(tallies)) {
      var label = tally == 0 ? CoverageLabel.NotCovered : CoverageLabel.FullyCovered;
      // For now we only identify branches at the line granularity,
      // which matches what `dafny generate-tests ... --coverage-report` does as well.
      var rangeToken = new TokenRange(
        new Token(token.line, 1) { Uri = token.Uri },
        new Token(token.line + 1, 1));
      coverageReport.LabelCode(rangeToken, label);
    }
  }

}
