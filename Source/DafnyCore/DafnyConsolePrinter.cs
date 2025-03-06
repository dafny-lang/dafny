using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using DafnyCore;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;

namespace Microsoft.Dafny;

public record AssertCmdPartialCopy(Boogie.IToken Tok, string Description, string Id);
public record VerificationRunResultPartialCopy(
  int VCNum,
  DateTime StartTime,
  TimeSpan RunTime,
  SolverOutcome Outcome,
  List<AssertCmdPartialCopy> Asserts,
  IEnumerable<TrackedNodeComponent> CoveredElements,
  IEnumerable<Axiom> AvailableAxioms,
  int ResourceCount);

public class DafnyConsolePrinter : ConsolePrinter {
  public new DafnyOptions Options {
    get => options;
    set {
      base.Options = value;
      options = value;
    }
  }

  private DafnyOptions options;

  public record ImplementationLogEntry(string Name, Boogie.IToken Tok);
  public record VerificationResultLogEntry(
    VcOutcome Outcome,
    TimeSpan RunTime,
    int ResourceCount,
    List<VerificationRunResultPartialCopy> VCResults,
    List<Counterexample> Counterexamples);
  public record ConsoleLogEntry(ImplementationLogEntry Implementation, VerificationResultLogEntry Result);

  public static VerificationResultLogEntry DistillVerificationResult(ImplementationRunResult verificationResult) {
    return new VerificationResultLogEntry(
      verificationResult.VcOutcome, verificationResult.End - verificationResult.Start,
      verificationResult.ResourceCount, verificationResult.RunResults.Select(DistillVCResult).ToList(), verificationResult.Errors);
  }

  public static VerificationRunResultPartialCopy DistillVCResult(VerificationRunResult r) {
    return new VerificationRunResultPartialCopy(r.VcNum, r.StartTime, r.RunTime, r.Outcome,
        r.Asserts.Select(a => new AssertCmdPartialCopy(a.tok, a.Description.SuccessDescription, GetId(a))).ToList(), r.CoveredElements,
        r.DeclarationsAfterPruning.OfType<Axiom>(), r.ResourceCount);

    string GetId(ICarriesAttributes construct) {
      var values = construct.FindAllAttributes("id");
      if (!values.Any()) {
        return "";
      }
      return (string)values.Last().Params.First();
    }
  }

  public ConcurrentBag<ConsoleLogEntry> VerificationResults { get; } = [];

  public override void AdvisoryWriteLine(TextWriter output, string format, params object[] args) {
    if (output == Console.Out) {
      int foregroundColor = (int)Console.ForegroundColor;
      Console.ForegroundColor = ConsoleColor.Yellow;
      output.WriteLine(format, args);
      Console.ForegroundColor = (ConsoleColor)foregroundColor;
    } else {
      output.WriteLine(format, args);
    }
  }



  public DafnyConsolePrinter(DafnyOptions options) {
    Options = options;
  }

  public override void ReportBplError(Boogie.IToken tok, string message, bool error, TextWriter tw, string category = null) {
    if (Options.Verbosity == CoreOptions.VerbosityLevel.Silent) {
      return;
    }

    var consoleReporter = new ConsoleErrorReporter(options);
    var dafnyToken = BoogieGenerator.ToDafnyToken(options.Get(Snippets.ShowSnippets), tok);
    if (message.StartsWith("Error: ")) {
      message = message.Substring("Error: ".Length);
    }
    consoleReporter.MessageCore(MessageSource.Verifier, error ? ErrorLevel.Error : ErrorLevel.Warning, null, dafnyToken,
      message);
  }

  public override void ReportEndVerifyImplementation(Implementation implementation, ImplementationRunResult result) {
    var impl = new ImplementationLogEntry(implementation.VerboseName, implementation.tok);
    VerificationResults.Add(new ConsoleLogEntry(impl, DistillVerificationResult(result)));
  }
}