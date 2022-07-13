using System;
using System.Collections.Generic;
using System.Linq;
using MediatR;
using OmniSharp.Extensions.LanguageServer.Protocol;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record FileVerificationStatus(
  DocumentUri Uri,
  int? Version,
  IReadOnlyList<NamedVerifiableStatus> NamedVerifiables) : IRequest {
  public override string ToString() {
    return $"{nameof(NamedVerifiables)}: {string.Join(", ", NamedVerifiables)}";
  }
}

/**
 * Groups Boogie verification tasks by named Dafny declarations such as:
 * methods,
 * functions,
 * data-types (whose default-value expressions are verified),
 * fields (whose initial value is verified)
 * types definitions (for example the verification of a witness of a subset type)
 */
public record NamedVerifiableStatus(Range NameRange, PublishedVerificationStatus Status) {
  public virtual bool Equals(NamedVerifiableStatus? other) {
    if (ReferenceEquals(null, other)) {
      return false;
    }

    if (ReferenceEquals(this, other)) {
      return true;
    }

    return NameRange.Equals(other.NameRange) && Status == other.Status;
  }

  public override int GetHashCode() {
    return HashCode.Combine(NameRange, (int)Status);
  }
}

public enum PublishedVerificationStatus {
  Stale = 0,    // Not scheduled to be run
  Queued = 1,   // Scheduled to be run but waiting for resources
  Running = 2,  // Currently running
  Error = 4,    // Finished and had errors
  Correct = 5,  // Finished and was correct
}