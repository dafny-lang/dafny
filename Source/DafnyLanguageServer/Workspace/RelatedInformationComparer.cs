using System;
using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class RelatedInformationComparer : IEqualityComparer<DiagnosticRelatedInformation> {
  public bool Equals(DiagnosticRelatedInformation? x, DiagnosticRelatedInformation? y) {
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

    return x.Location.Equals(y.Location) && x.Message == y.Message;
  }

  public int GetHashCode(DiagnosticRelatedInformation obj) {
    return HashCode.Combine(obj.Location, obj.Message);
  }
}