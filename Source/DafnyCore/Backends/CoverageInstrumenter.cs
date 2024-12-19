using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public class CoverageInstrumenter {
  private readonly SinglePassCodeGenerator codeGenerator;
  private List<(IOrigin, string)>/*?*/ legend;  // non-null implies options.CoverageLegendFile is non-null
  private string talliesFilePath;

  public CoverageInstrumenter(SinglePassCodeGenerator codeGenerator) {
    this.codeGenerator = codeGenerator;
    if (codeGenerator.Options?.CoverageLegendFile != null
        || codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      legend = new List<(IOrigin, string)>();
    }

    if (codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      talliesFilePath = Path.GetTempFileName();
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

  public void WriteLegendFile() {
    if (codeGenerator.Options?.CoverageLegendFile != null) {
      var filename = codeGenerator.Options.CoverageLegendFile;
      Contract.Assert(filename != null);
      TextWriter wr = filename == "-" ? codeGenerator.Options.OutputWriter : new StreamWriter(new FileStream(Path.GetFullPath(filename), FileMode.Create));
      {
        for (var i = 0; i < legend.Count; i++) {
          var e = legend[i];
          wr.WriteLine($"{i}: {e.Item1.TokenToString(codeGenerator.Options)}: {e.Item2}");
        }
      }
      legend = null;
    }
  }

  public void PopulateCoverageReport(CoverageReport coverageReport) {
    var coverageReportDir = codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport);
    if (coverageReportDir != null) {
      var tallies = File.ReadLines(talliesFilePath).Select(int.Parse).ToArray();
      foreach (var ((token, _), tally) in legend.Zip(tallies)) {
        var label = tally == 0 ? CoverageLabel.NotCovered : CoverageLabel.FullyCovered;
        // For now we only identify branches at the line granularity,
        // which matches what `dafny generate-tests ... --coverage-report` does as well.
        var rangeToken = new SourceOrigin(new Token(token.line, 1), new Token(token.line + 1, 0));
        rangeToken.Uri = token.Uri;
        coverageReport.LabelCode(rangeToken, label);
      }
    }
  }

}
