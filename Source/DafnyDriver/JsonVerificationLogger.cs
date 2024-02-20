using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
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

  private static JsonNode SerializeAssertion(AssertCmd assertion) {
    return new JsonObject {
      ["filename"] = assertion.tok.filename,
      ["line"] = assertion.tok.line,
      ["col"] = assertion.tok.col,
      ["description"] = assertion.Description.SuccessDescription
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

  private JsonNode SerializeVcResult(IEnumerable<ProofDependency> potentialDependencies, VerificationRunResult vcResult) {
    var result = new JsonObject {
      ["vcNum"] = vcResult.VcNum,
      ["outcome"] = SerializeOutcome(vcResult.Outcome),
      ["runTime"] = SerializeTimeSpan(vcResult.RunTime),
      ["resourceCount"] = vcResult.ResourceCount,
      ["assertions"] = new JsonArray(vcResult.Asserts.Select(SerializeAssertion).ToArray()),
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

  private JsonNode SerializeVerificationResult(Implementation impl, ImplementationRunResult verificationResult) {
    var trackProofDependencies =
      verificationResult.VcOutcome == VcOutcome.Correct &&
      verificationResult.RunResults.Any(vcResult => vcResult.CoveredElements.Any());
    var potentialDependencies =
      trackProofDependencies ? depManager.GetPotentialDependenciesForDefinition(impl.Name) : null;
    var result = new JsonObject {
      ["name"] = impl.Name,
      ["outcome"] = SerializeOutcome(verificationResult.VcOutcome),
      ["runTime"] = SerializeTimeSpan(verificationResult.End - verificationResult.Start),
      ["resourceCount"] = verificationResult.ResourceCount,
      ["vcResults"] = new JsonArray(verificationResult.RunResults.Select(r => SerializeVcResult(potentialDependencies, r)).ToArray())
    };
    if (potentialDependencies is not null) {
      result["programElements"] = new JsonArray(potentialDependencies.Select(SerializeProofDependency).ToArray());
    }
    return result;
  }

  private JsonObject SerializeVerificationResults(IEnumerable<ImplementationRunResult> verificationResults) {
    return new JsonObject {
      ["verificationResults"] = new JsonArray(verificationResults.Select(SerializeVerificationResult).ToArray())
    };
  }

  public void LogResults(IEnumerable<ImplementationRunResult> verificationResults) {
    tw.Write(SerializeVerificationResults(verificationResults).ToJsonString());
  }
}