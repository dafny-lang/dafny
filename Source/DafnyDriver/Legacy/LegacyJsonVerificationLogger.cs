using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json.Nodes;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class LegacyJsonVerificationLogger {
  private TextWriter tw;
  private readonly TextWriter outWriter;
  private readonly ProofDependencyManager depManager;

  public LegacyJsonVerificationLogger(ProofDependencyManager depManager, TextWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  class DummyProofObligationDescription : Boogie.ProofObligationDescription {
    public DummyProofObligationDescription(string success) {
      SuccessDescription = success;
    }

    public override string SuccessDescription { get; }

    public override string ShortDescription => throw new NotSupportedException();
  }


  private JsonNode SerializeVcResult(IEnumerable<ProofDependency> potentialDependencies, VerificationRunResultPartialCopy verificationRunResult) {
    var runResult = VCResultLogEntryToPartialVerificationRunResult(verificationRunResult);
    return JsonVerificationLogger.SerializeVcResult(depManager, potentialDependencies?.ToList(), runResult);
  }

  public static VerificationTaskResult VCResultLogEntryToPartialVerificationRunResult(VerificationRunResultPartialCopy verificationRunResult) {
    var mockNumber = 42;
    var mockAsserts = verificationRunResult.Asserts.Select(t => new AssertCmd(t.Tok, null, new DummyProofObligationDescription(t.Description)));
    var runResult = new VerificationRunResult(verificationRunResult.VCNum, mockNumber, verificationRunResult.StartTime, verificationRunResult.Outcome, verificationRunResult.RunTime, mockNumber, null!,
      mockAsserts.ToList(), verificationRunResult.CoveredElements, verificationRunResult.ResourceCount, null, new List<Boogie.Declaration>());
    return new VerificationTaskResult(null, runResult);
  }

  private static JsonNode SerializeTimeSpan(TimeSpan timeSpan) {
    return timeSpan.ToString();
  }

  private static JsonNode SerializeOutcome(SolverOutcome outcome) {
    return outcome.ToString();
  }
  private static JsonNode SerializeOutcome(VcOutcome outcome) {
    return outcome.ToString();
  }

  private JsonNode SerializeVerificationResult(DafnyConsolePrinter.ConsoleLogEntry logEntry) {
    var (impl, verificationResult) = logEntry;
    var trackProofDependencies =
      verificationResult.Outcome == VcOutcome.Correct &&
      verificationResult.VCResults.Any(vcResult => vcResult.CoveredElements.Any());
    var potentialDependencies =
      trackProofDependencies ? depManager.GetPotentialDependenciesForDefinition(impl.Name) : null;
    var result = new JsonObject {
      ["name"] = impl.Name,
      ["outcome"] = SerializeOutcome(verificationResult.Outcome),
      ["runTime"] = SerializeTimeSpan(verificationResult.RunTime),
      ["resourceCount"] = verificationResult.ResourceCount,
      ["vcResults"] = new JsonArray(verificationResult.VCResults.Select(r => SerializeVcResult(potentialDependencies, r)).ToArray())
    };
    if (potentialDependencies is not null) {
      result["programElements"] = new JsonArray(potentialDependencies.Select(JsonVerificationLogger.SerializeProofDependency).ToArray());
    }
    return result;
  }

  private JsonObject SerializeVerificationResults(IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults) {
    return new JsonObject {
      ["verificationResults"] = new JsonArray(verificationResults.Select(SerializeVerificationResult).ToArray())
    };
  }

  public void LogResults(IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults) {
    tw.Write(SerializeVerificationResults(verificationResults).ToJsonString());
  }
}