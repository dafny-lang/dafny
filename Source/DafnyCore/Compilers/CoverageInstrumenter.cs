using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public class CoverageInstrumenter {
  private readonly SinglePassCompiler compiler;
  private List<(IToken, string)>/*?*/ legend;  // non-null implies options.CoverageLegendFile is non-null
  private string talliesFilePath;

  public CoverageInstrumenter(SinglePassCompiler compiler) {
    this.compiler = compiler;
    if (compiler.Options?.CoverageLegendFile != null
        || compiler.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      legend = new List<(IToken, string)>();
    }

    if (compiler.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      talliesFilePath = Path.GetTempFileName();
    }
  }

  public bool IsRecording {
    get => legend != null;
  }

  public void Instrument(IToken tok, string description, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Record({0})", legend.Count);
      compiler.EndStmt(wr);
      legend.Add((tok, description));
    }
  }

  public void UnusedInstrumentationPoint(IToken tok, string description) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    if (legend != null) {
      legend.Add((tok, description));
    }
  }

  public void InstrumentExpr(IToken tok, string description, bool resultValue, ConcreteSyntaxTree wr) {
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
        wr.Write($", \"{talliesFilePath}\"");
      }
      wr.Write(")");
      compiler.EndStmt(wr);
    }
  }

  public void EmitTearDown(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.TearDown()");
      compiler.EndStmt(wr);
    }
  }

  public void WriteLegendFile() {
    if (compiler.Options?.CoverageLegendFile != null) {
      var filename = compiler.Options.CoverageLegendFile;
      Contract.Assert(filename != null);
      TextWriter wr = filename == "-" ? compiler.Options.OutputWriter : new StreamWriter(new FileStream(Path.GetFullPath(filename), System.IO.FileMode.Create));
      {
        for (var i = 0; i < legend.Count; i++) {
          var e = legend[i];
          wr.WriteLine($"{i}: {e.Item1.TokenToString(compiler.Options)}: {e.Item2}");
        }
      }
      legend = null;
    }
  }

  public void PopulateCoverageReport(CoverageReport report) {
    var tallies = File.ReadLines(talliesFilePath).Select(int.Parse).ToArray();
    foreach (var ((token, _), tally) in legend.Zip(tallies)) {
      var label = tally == 0 ? CoverageLabel.NotCovered : CoverageLabel.FullyCovered;
      // For now we only identify branches at the line granularity,
      // which matches what `dafny generate-tests ... --coverage-report` does as well.
      var rangeToken = new RangeToken(new Token(token.line, 1), new Token(token.line + 1, 0));
      rangeToken.Uri = token.Uri;
      report.LabelCode(rangeToken, label);
    }
  }

}
