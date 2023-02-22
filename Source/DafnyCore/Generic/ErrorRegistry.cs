// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Plugins;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

public delegate List<DafnyCodeAction> ActionSignature(IDafnyCodeActionInput input, Diagnostic diagnostic, Range range);

public static class ErrorRegistry {

#nullable enable
  public static List<ActionSignature>? GetAction(string? errorId) {
    return errorId != null && codeActionMap.ContainsKey(errorId) ? new List<ActionSignature> { codeActionMap[errorId] } : null;
  }
#nullable disable

  public static ActionSignature Insert(string newContent, string title) {
    return (input, diagnostic, range) => InsertAction(title, diagnostic, range, newContent);
  }

  public static ActionSignature Replace(string newContent, string overrideTitle = null) {
    if (overrideTitle == null) {
      return (input, diagnostic, range) => ReplacementAction(input, diagnostic, range, newContent);
    }
    return (input, diagnostic, range) => ReplacementAction(overrideTitle, diagnostic, range, newContent);
  }
  
  public static ActionSignature Replacements(IEnumerable<(string NewContent, string Title)> replacements) {
    return (input, diagnostic, range) => {
      var actions = new List<DafnyCodeAction>();
      foreach (var replacement in replacements) {
        var edit = new[] {new DafnyCodeActionEdit(range, replacement.NewContent)};
        var action = new InstantDafnyCodeAction(replacement.Title, new List<Diagnostic> {diagnostic}, edit);
        actions.Add(action);
      }

      return actions;
    };
  }

  /// <summary>
  /// Default title is "remove'X'" where X is the content of the range
  /// </summary>
  public static ActionSignature Remove(string overrideTitle = null) {
    if (overrideTitle == null) {
      return RemoveAction;
    }

    return (input, diagnostic, range) => RemoveAction(overrideTitle, diagnostic, range);
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

  private static List<DafnyCodeAction> ReplacementAction(string title, Diagnostic diagnostic, Range range, string newText) {
    var edit = new[] { new DafnyCodeActionEdit(range, newText) };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  private static List<DafnyCodeAction> ReplacementAction(IDafnyCodeActionInput input, Diagnostic diagnostic, Range range, string newText) {
    string toBeReplaced = input.Extract(range).Trim();
    string title = "replace '" + toBeReplaced + "' with '" + newText + "'";
    var edit = new[] { new DafnyCodeActionEdit(range, newText) };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  private static List<DafnyCodeAction> InsertAction(string title, Diagnostic diagnostic, Range range, string newText) {
    var edit = new[] { new DafnyCodeActionEdit(new Range(range.End, range.End), newText) };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  private static List<DafnyCodeAction> RemoveAction(string title, Diagnostic diagnostic, Range range) {
    var edit = new[] { new DafnyCodeActionEdit(range, "") };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
  }

  private static List<DafnyCodeAction> RemoveAction(IDafnyCodeActionInput input, Diagnostic diagnostic, Range range) {
    string toBeRemoved = input.Extract(range).Trim();
    string title = "remove '" + toBeRemoved + "'";
    var edit = new[] { new DafnyCodeActionEdit(range, "") };
    var action = new InstantDafnyCodeAction(title, new List<Diagnostic> { diagnostic }, edit);
    return new List<DafnyCodeAction> { action };
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


