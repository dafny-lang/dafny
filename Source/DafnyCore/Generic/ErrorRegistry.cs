// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public record DafnyPosition(int Line, int Column) : IComparable<DafnyPosition> {
  public int CompareTo(DafnyPosition other) {
    var lineComparison = Line.CompareTo(other.Line);
    if (lineComparison != 0) {
      return lineComparison;
    }

    return Column.CompareTo(other.Column);
  }
}

public record DafnyRange(DafnyPosition Start, DafnyPosition ExclusiveEnd) {
  public bool Contains(DafnyPosition position) {
    return Start.LessThanOrEquals(position) && position.LessThanOrEquals(ExclusiveEnd);
  }
}

/// <summary>
/// A quick fix replaces a range with the replacing text.
/// </summary>
/// <param name="Range">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="Replacement"></param>
public record DafnyCodeActionEdit(DafnyRange Range, string Replacement = "") {
  public DafnyCodeActionEdit(TokenRange rangeOrigin, string replacement = "", bool includeTrailingWhitespace = false)
    : this(rangeOrigin.ToDafnyRange(includeTrailingWhitespace), replacement) {
  }
}


public delegate List<DafnyAction> ActionSignature(TokenRange range);
public delegate bool TokenPredicate(IOrigin token);

public record DafnyAction(string Title, IReadOnlyList<DafnyCodeActionEdit> Edits);

public static class ErrorRegistry {

  // Replace any NoneId by ParseErrors.p_... or ResolutionErrors.r_
  public static string NoneId => "none";
#nullable enable
  public static List<ActionSignature>? GetAction(string? errorId) {
    return errorId != null && codeActionMap.TryGetValue(errorId, out var value) ? [value] : null;
  }
#nullable disable

  public static ActionSignature InsertAfter(string newContent, string title) {
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


  public static DafnyCodeActionEdit[] OneEdit(TokenRange range, string newContent, bool includeTrailingWhitespace = false) {
    return [new DafnyCodeActionEdit(range, newContent, includeTrailingWhitespace)];
  }

  public static DafnyAction OneAction(string title, TokenRange range, string newContent, bool includeTrailingWhitespace = false) {
    return new(title, new[] { new DafnyCodeActionEdit(range, newContent, includeTrailingWhitespace) });
  }

  public static TokenRange IncludeComma(TokenRange range) {
    if (range.EndToken.Next.val == ",") {
      return new TokenRange(range.StartToken, range.EndToken.Next);
    }
    if (range.StartToken.Prev.val == ",") {
      return new TokenRange(range.StartToken.Prev, range.EndToken);
    }
    return range;
  }

  public static TokenRange ExpandStart(TokenRange range, TokenPredicate pred, bool include) {
    var t = range.StartToken;
    Token p = null;
    while (!pred(t)) {
      p = t;
      t = t.Prev;
      if (t == null) {
        return range;
      }
    }
    return new TokenRange(include ? t : p!, range.EndToken);
  }

  public static TokenRange ExpandEnd(TokenRange range, TokenPredicate pred, bool include) {
    var t = range.EndToken;
    Token p = null;
    while (!pred(t)) {
      p = t;
      t = t.Prev;
      if (t == null) {
        return range;
      }
    }
    return new TokenRange(range.StartToken, include ? t : p);
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

  private static List<DafnyAction> ReplacementAction(string title, TokenRange range, string newText) {
    var edit = new[] { new DafnyCodeActionEdit(range, newText) };
    var action = new DafnyAction(title, edit);
    return [action];
  }

  private static List<DafnyAction> ReplacementAction(TokenRange range, string newText) {
    string toBeReplaced = range.PrintOriginal();
    string title = "replace '" + toBeReplaced + "' with '" + newText + "'";
    return ReplacementAction(title, range, newText);
  }

  private static List<DafnyAction> InsertAction(string title, TokenRange range, string newText) {
    var edits = new[] { new DafnyCodeActionEdit(range, range.PrintOriginal() + newText) };
    var action = new DafnyAction(title, edits);
    return [action];
  }

  private static List<DafnyAction> RemoveAction(string title, TokenRange range, bool includeTrailingSpaces) {
    var edit = new[] { new DafnyCodeActionEdit(range, "", includeTrailingSpaces) };
    var action = new DafnyAction(title, edit);
    return [action];
  }

  private static List<DafnyAction> RemoveAction(TokenRange range, bool includeTrailingSpaces) {
    string toBeRemoved = range.PrintOriginal();
    string title = "remove '" + toBeRemoved + "'";
    return RemoveAction(title, range, includeTrailingSpaces);
  }

#nullable enable
  public static string? GetDetail(string? errorId) {
    return errorId == null ? null : errorDetailMap.GetValueOrDefault(errorId);
  }
#nullable disable
}


