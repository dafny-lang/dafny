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
public record DafnyCodeActionEdit(DafnyRange Range, string Replacement = "") {
  public DafnyCodeActionEdit(RangeToken rangeToken, string replacement = "", bool includeTrailingWhitespace = false)
    : this(rangeToken.ToDafnyRange(includeTrailingWhitespace), replacement) {
  }
}


public delegate List<DafnyAction> ActionSignature(RangeToken range);
public delegate bool TokenPredicate(IToken token);

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

  public static ActionSignature InsertBefore(string newContent) {
    return range => ReplacementAction("insert '" + newContent + "'", range, newContent + range.PrintOriginal());
  }

  public static ActionSignature Replace(string newContent, string overrideTitle = null) {
    if (overrideTitle == null) {
      return range => ReplacementAction("replace '" + range.PrintOriginal() + "' with '" + newContent + "'", range, newContent);
    }
    return range => ReplacementAction(overrideTitle, range, newContent);
  }


  public static DafnyCodeActionEdit[] OneEdit(RangeToken range, string newcontent, bool includeTrailingWhitespace = false) {
    return new[] { new DafnyCodeActionEdit(range, newcontent, includeTrailingWhitespace) };
  }

  public static DafnyAction OneAction(string title, RangeToken range, string newcontent, bool includeTrailingWhitespace = false) {
    return new(title, new[] { new DafnyCodeActionEdit(range, newcontent, includeTrailingWhitespace) });
  }

  public static RangeToken IncludeComma(RangeToken range) {
    if (range.EndToken.Next.val == ",") return new RangeToken(range.StartToken, range.EndToken.Next);
    if (range.StartToken.Prev.val == ",") return new RangeToken(range.StartToken.Prev, range.EndToken);
    return range;
  }

  public static RangeToken ExpandStart(RangeToken range, TokenPredicate pred, bool include) {
    var t = range.StartToken;
    IToken p = null;
    while (!pred(t)) {
      p = t;
      t = t.Prev;
      if (t == null) return range;
    }
    if (include) return new RangeToken(t, range.EndToken);
    return new RangeToken(p, range.EndToken);
  }

  public static RangeToken ExpandEnd(RangeToken range, TokenPredicate pred, bool include) {
    var t = range.EndToken;
    IToken p = null;
    while (!pred(t)) {
      p = t;
      t = t.Prev;
      if (t == null) return range;
    }
    if (include) return new RangeToken(range.StartToken, t);
    return new RangeToken(range.StartToken, p);
  }

  public static ActionSignature Replacements(IEnumerable<(string NewContent, string Title)> replacements) {
    return range => {
      var actions = new List<DafnyAction>();
      foreach (var replacement in replacements) {
        var edit = new[] { new DafnyCodeActionEdit(range, replacement.NewContent) };
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
    var edit = new[] { new DafnyCodeActionEdit(range, newText) };
    var action = new DafnyAction(title, edit);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> ReplacementAction(RangeToken range, string newText) {
    string toBeReplaced = range.PrintOriginal();
    string title = "replace '" + toBeReplaced + "' with '" + newText + "'";
    return ReplacementAction(title, range, newText);
  }

  private static List<DafnyAction> InsertAction(string title, RangeToken range, string newText) {
    var edits = new[] { new DafnyCodeActionEdit(range, range.PrintOriginal() + newText) };
    var action = new DafnyAction(title, edits);
    return new List<DafnyAction> { action };
  }

  private static List<DafnyAction> RemoveAction(string title, RangeToken range, bool includeTrailingSpaces) {
    var edit = new[] { new DafnyCodeActionEdit(range, "", includeTrailingSpaces) };
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


