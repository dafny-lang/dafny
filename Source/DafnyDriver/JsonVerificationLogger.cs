using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json.Nodes;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using VC;

namespace Microsoft.Dafny;

public class JsonVerificationLogger {
  private TextWriter tw;
  private readonly TextWriter outWriter;
  private readonly ProofDependencyManager depManager;

  public JsonVerificationLogger(ProofDependencyManager depManager, TextWriter outWriter) {
    this.depManager = depManager;
    this.outWriter = outWriter;
  }

  public void Initialize(Dictionary<string, string> parameters) {
    tw = parameters.TryGetValue("LogFileName", out string filename) ? new StreamWriter(filename) : outWriter;
  }

  private static JsonNode SerializeAssertion(Microsoft.Boogie.IToken tok, string description) {
    return new JsonObject {
      ["filename"] = tok.filename,
      ["line"] = tok.line,
      ["col"] = tok.col,
      ["description"] = description
    };
  }

  private JsonNode SerializeProofDependency(ProofDependency dependency) {
    return new JsonObject {
      ["startFile"] = dependency.Range.StartToken.Filepath,
      ["startLine"] = dependency.Range.StartToken.line,
      ["startCol"] = dependency.Range.StartToken.col,
      ["endFile"] = dependency.Range.EndToken.Filepath,
      ["endLine"] = dependency.Range.EndToken.line,
      ["endCol"] = dependency.Range.EndToken.col,
      ["description"] = dependency.Description,
      ["originalText"] = dependency.OriginalString()
    };
  }

  private JsonNode SerializeVcResult(IEnumerable<ProofDependency> potentialDependencies, DafnyConsolePrinter.VCResultLogEntry vcResult) {
    var result = new JsonObject {
      ["vcNum"] = vcResult.VCNum,
      ["outcome"] = SerializeOutcome(vcResult.Outcome),
      ["runTime"] = SerializeTimeSpan(vcResult.RunTime),
      ["resourceCount"] = vcResult.ResourceCount,
      ["assertions"] = new JsonArray(vcResult.Asserts.Select(x => SerializeAssertion(x.Tok, x.Description)).ToArray()),
    };
    if (potentialDependencies is not null) {
      var fullDependencies = depManager.GetOrderedFullDependencies(vcResult.CoveredElements);
      var fullDependencySet = fullDependencies.ToHashSet();
      var unusedDependencies = potentialDependencies.Where(dep => !fullDependencySet.Contains(dep));
      result["coveredElements"] = new JsonArray(fullDependencies.Select(SerializeProofDependency).ToArray());
      result["uncoveredElements"] = new JsonArray(unusedDependencies.Select(SerializeProofDependency).ToArray());
    }
    return result;
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
      result["programElements"] = new JsonArray(potentialDependencies.Select(SerializeProofDependency).ToArray());
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