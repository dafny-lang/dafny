// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;

namespace Microsoft.Dafny;

public record DafnyPosition(int Line, int Column);

public record DafnyRange(DafnyPosition Start, DafnyPosition ExclusiveEnd);

/// <summary>
/// A quick fix replaces a range with the replacing text.
/// </summary>
/// <param name="Range">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="Replacement"></param>
public record DafnyCodeActionEdit(DafnyRange Range, string Replacement = "");

public delegate List<DafnyAction> ActionSignature(RangeToken range);

public record DafnyAction(string Title, IReadOnlyList<DafnyCodeActionEdit> Edits);

public static class ErrorRegistry {

  public static string NoneId => "none";
#nullable enable
  public static List<ActionSignature>? GetAction(string? errorId) {
    return errorId != null && codeActionMap.ContainsKey(errorId) ? new List<ActionSignature> { codeActionMap[errorId] } : null;
  }
#nullable disable

  public static ActionSignature Insert(string newContent, string title) {
    return range => InsertAction(title, range, newContent);
  }

  public static ActionSignature Replace(string newContent, string overrideTitle = null) {
    if (overrideTitle == null) {
      return range => ReplacementAction(range.PrintOriginal(), range, newContent);
    }
    return range => ReplacementAction(overrideTitle, range, newContent);
  }

  public static ActionSignature Replacements(IEnumerable<(string NewContent, string Title)> replacements) {
    return range => {
      var actions = new List<DafnyAction>();
      foreach (var replacement in replacements) {
        var edit = new[] { new DafnyCodeActionEdit(range.ToDafnyRange(), replacement.NewContent) };
        var action = new DafnyAction(replacement.Title, edit);
        actions.Add(action);
      }

      return actions;
    };
  }

  /// <summary>
  /// Default title is "remove'X'" where X is the content of the range
  /// </summary>
  public static ActionSignature Remove(bool removeTrailingSpaces, string overrideTitle = null) {
    if (overrideTitle == null) {
      return range => RemoveAction(range, removeTrailingSpaces);
    }

    return range => RemoveAction(overrideTitle, range, removeTrailingSpaces);
  }


  /// <summary>
  /// Maps an errorID (error code) to a code action and explanatory text (which could be moderately lengthy)
  /// </summary>
  private static readonly Dictionary<string, string> errorDetailMap = new();
  private static Dictionary<string, ActionSignature> codeActionMap = new();

  public static void Add(object errorId, string detail, ActionSignature codeAction = null) {
    errorDetailMap.Add(errorId.ToString()!, detail);
    if (codeAction != null) {
      codeActionMap.Add(errorId.ToString()!, codeAction);
    }
  }

  private static List<DafnyAction> ReplacementAction(string title, RangeToken range, string newText) {
    var edit = new[] { new DafnyCodeActionEdit(range.ToDafnyRange(), newText) };
    var action = new DafnyAction(title, edit);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> ReplacementAction(RangeToken range, string newText) {
    string toBeReplaced = range.PrintOriginal();
    string title = "replace '" + toBeReplaced + "' with '" + newText + "'";
    var edit = new[] { new DafnyCodeActionEdit(range.ToDafnyRange(), newText) };
    var action = new DafnyAction(title, edit);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> InsertAction(string title, RangeToken range, string newText) {
    var edits = new[] { new DafnyCodeActionEdit(range.ToDafnyRange(), newText) };
    var action = new DafnyAction(title, edits);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> RemoveAction(string title, RangeToken range, bool includeTrailingSpaces) {
    var edit = new[] { new DafnyCodeActionEdit(range.ToDafnyRange(includeTrailingSpaces), "") };
    var action = new DafnyAction(title, edit);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> RemoveAction(RangeToken range, bool includeTrailingSpaces) {
    string toBeRemoved = range.PrintOriginal();
    string title = "remove '" + toBeRemoved + "'";
    return RemoveAction(title, range, includeTrailingSpaces);
  }

#nullable enable
  public static string? GetDetail(string? errorId) {
    if (errorId == null) {
      return null;
    }
    if (errorDetailMap.TryGetValue(errorId, out var result)) {
      return result;
    }
    return null;
  }
#nullable disable
}


