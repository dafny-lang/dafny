using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny.Compilers;

public abstract class ConcreteSinglePassCompiler : GenericSinglePassCompiler<ConcreteSyntaxTree> {
  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    Coverage = new CoverageInstrumenter(this);
  }
}

public class CoverageInstrumenter {
  private readonly ConcreteSinglePassCompiler compiler;
  private List<(IToken, string)>/*?*/ legend;  // non-null implies DafnyOptions.O.CoverageLegendFile is non-null

  public CoverageInstrumenter(ConcreteSinglePassCompiler compiler) {
    this.compiler = compiler;
    if (DafnyOptions.O.CoverageLegendFile != null) {
      legend = new List<(IToken, string)>();
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
      wr.Write("DafnyProfiling.CodeCoverage.Setup({0})", legend.Count);
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
    if (legend != null) {
      var filename = DafnyOptions.O.CoverageLegendFile;
      Contract.Assert(filename != null);
      TextWriter wr = filename == "-" ? System.Console.Out : new StreamWriter(new FileStream(Path.GetFullPath(filename), System.IO.FileMode.Create));
      {
        for (var i = 0; i < legend.Count; i++) {
          var e = legend[i];
          wr.WriteLine("{0}: {1}({2},{3}): {4}", i, e.Item1.Filename, e.Item1.line, e.Item1.col, e.Item2);
        }
      }
      legend = null;
    }
  }
}