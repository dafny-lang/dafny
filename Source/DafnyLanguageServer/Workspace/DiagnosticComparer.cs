using System;
using System.Collections.Generic;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class DiagnosticComparer : IEqualityComparer<Diagnostic> {
  private readonly RelatedInformationComparer relatedInformationComparer = new();
  public bool Equals(Diagnostic? x, Diagnostic? y) {
    if (ReferenceEquals(x, y)) {
      return true;
    }

    if (ReferenceEquals(x, null)) {
      return false;
    }

    if (ReferenceEquals(y, null)) {
      return false;
    }

    if (x.GetType() != y.GetType()) {
      return false;
    }

    if (ReferenceEquals(x.RelatedInformation, null) != ReferenceEquals(y.RelatedInformation, null)) {
      return false;
    }

    return x.Range.Equals(y.Range) && x.Severity == y.Severity && Nullable.Equals(x.Code, y.Code) &&
           Equals(x.CodeDescription, y.CodeDescription) &&
           x.Source == y.Source && x.Message == y.Message &&
           Equals(x.Tags, y.Tags) &&
           (ReferenceEquals(x.RelatedInformation, null) || x.RelatedInformation!.SequenceEqual(y.RelatedInformation!, relatedInformationComparer)) &&
           Equals(x.Data, y.Data);
  }

  public int GetHashCode(Diagnostic obj) {
    var hashCode = new HashCode();
    hashCode.Add(obj.Range);
    hashCode.Add(obj.Severity);
    hashCode.Add(obj.Code);
    hashCode.Add(obj.CodeDescription);
    hashCode.Add(obj.Source);
    hashCode.Add(obj.Message);
    hashCode.Add(obj.Tags);
    foreach (var info in obj.RelatedInformation ?? Enumerable.Empty<DiagnosticRelatedInformation>()) {
      hashCode.Add(relatedInformationComparer.GetHashCode(info));
    }
    hashCode.Add(obj.Data);
    return hashCode.ToHashCode();
  }
}