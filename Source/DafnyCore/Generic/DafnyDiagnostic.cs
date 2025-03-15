#nullable enable
using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public record DafnyDiagnostic(MessageSource Source, string ErrorId, TokenRange Range, string Message, ErrorLevel Level,
  IReadOnlyList<DafnyRelatedInformation> RelatedInformation) : IComparable<DafnyDiagnostic> {
  public int CompareTo(DafnyDiagnostic? other) {
    if (other == null) {
      return 1;
    }
    var r0 = Range.CompareTo(other.Range);
    if (r0 != 0) {
      return r0;
    }

    for (var index = 0; index < RelatedInformation.Count; index++) {
      if (other.RelatedInformation.Count > index) {
        var r1 = RelatedInformation[index].Range.CompareTo(other.RelatedInformation[index].Range);
        if (r1 != 0) {
          return r1;
        }
      } else {
        return 1;
      }
    }

    if (other.RelatedInformation.Count > RelatedInformation.Count) {
      return -1;
    }

    return 0;
  }
}

class OriginCenterComparer : IComparer<IOrigin> {
  public static readonly OriginCenterComparer Instance = new();

  public int Compare(IOrigin? x, IOrigin? y) {
    if (x == null) {
      return -1;
    }

    if (y == null) {
      return 1;
    }

    if (x is NestedOrigin nestedX && y is NestedOrigin nestedY) {
      var outer = Compare(nestedX.Outer, nestedY.Outer);
      if (outer != 0) {
        return outer;
      }

      return Compare(nestedX.Inner, nestedY.Inner);
    }
    return x.Center.CompareTo(y.Center);
  }
}