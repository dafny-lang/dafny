#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Resources;
using System.Text.RegularExpressions;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public record DafnyDiagnostic(MessageSource Source, string ErrorId, TokenRange Range, IReadOnlyList<string> MessageParts, ErrorLevel Level,
  IReadOnlyList<DafnyRelatedInformation> RelatedInformation) : IComparable<DafnyDiagnostic> {

  public string Message => MessageFromParts(ErrorId, MessageParts);

  private static readonly IDictionary<string, string> MessageIdToMessage = new Dictionary<string, string>();

  static DafnyDiagnostic() {
    InitializeMessageIdToMessage();
  }

  private static void InitializeMessageIdToMessage() {
    var assembly = Assembly.GetExecutingAssembly();
    using Stream stream = assembly.GetManifestResourceStream("DafnyCore.assets.messages.txt")!;
    using StreamReader reader = new StreamReader(stream);
    while (true) {
      var line = reader.ReadLine();
      if (line == null) {
        break;
      }
      var split = line.Split("=");
      MessageIdToMessage.Add(split[0], split[1]);
    }
  }

  public static string MessageFromParts(string errorId, IReadOnlyList<object> messageParts) {
    var formatMsg = GetFormatMsgAndRemainingParts(errorId, ref messageParts);
    if (messageParts.Count > 0) {
      return string.Format(formatMsg, messageParts.ToArray());
    } else {
      return formatMsg;
    }
  }

  public static string GetFormatMsgAndRemainingParts(string errorId, ref IReadOnlyList<object> messageParts) {
    if (string.IsNullOrEmpty(errorId) || !MessageIdToMessage.TryGetValue(errorId, out var formatMsg)) {
      formatMsg = (string)messageParts.First();
      messageParts = messageParts.Skip(1).ToList();
    }

    return formatMsg;
  }

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