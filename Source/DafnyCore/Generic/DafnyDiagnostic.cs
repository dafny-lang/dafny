#nullable enable
using System;
using System.Collections.Generic;
using System.Net;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

public class LocationComparer : IComparer<Location> {
  public static readonly LocationComparer Instance = new();
  public int Compare(Location? x, Location? y) {
    if (x == null) {
      if (y == null) {
        return 0;
      }

      return -1;
    }

    if (y == null) {
      return 1;
    }

    return RangeComparer.Instance.Compare(x.Range, y.Range);
  }
}

public class RangeComparer : IComparer<Range> {
  public static readonly RangeComparer Instance = new();
  public int Compare(Range? x, Range? y) {
    if (x == null) {
      if (y == null) {
        return 0;
      }

      return -1;
    }

    if (y == null) {
      return 1;
    }
    var startResult = x.Start.CompareTo(y);
    return startResult == 0 ? x.End.CompareTo(y.End) : startResult;
  }
}

public record DafnyDiagnostic(MessageSource Source, string ErrorId, Location? Token, string Message, ErrorLevel Level,
  IReadOnlyList<DafnyRelatedInformation> RelatedInformation) : IComparable<DafnyDiagnostic> {
  public int CompareTo(DafnyDiagnostic? other) {
    if (other == null) {
      return 1;
    }
    var r0 = LocationComparer.Instance.Compare(Token, other.Token);
    if (r0 != 0) {
      return r0;
    }

    for (var index = 0; index < RelatedInformation.Count; index++) {
      if (other.RelatedInformation.Count > index) {
        var r1 = LocationComparer.Instance.Compare(RelatedInformation[index].Token, other.RelatedInformation[index].Token);
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