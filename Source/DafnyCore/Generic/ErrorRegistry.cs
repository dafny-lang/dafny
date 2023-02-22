// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Plugins;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny;

/// <summary>
/// Describe a single suggestion made to the user, where edits can be
/// computed lazily.
/// If the edits can be provided instantly, you can use the derived class
/// `new InstantDafnyCodeAction(title, edits)`
/// </summary>
public abstract class DafnyCodeAction {
  // The title to display in the quickfix interface
  public readonly string Title;

  public readonly Container<Diagnostic> Diagnostics;

  protected DafnyCodeAction(string title) {
    Title = title;
    Diagnostics = new();
  }

  protected DafnyCodeAction(string title, Container<Diagnostic> diagnostics) {
    Title = title;
    Diagnostics = diagnostics;
  }

  // Edits are all performed at the same time
  // They are lazily invoked, so that they can be as complex as needed.
  public abstract IEnumerable<DafnyCodeActionEdit> GetEdits();
}

/// <summary>
/// A quick fix replaces a range with the replacing text.
/// </summary>
/// <param name="Range">The range to replace. The start is given by the token's start, and the length is given by the val's length.</param>
/// <param name="Replacement"></param>
public record DafnyCodeActionEdit(Range Range, string Replacement = "");

#nullable enable
public interface IDafnyCodeActionInput {
  /// <summary>
  /// The URI of the document being considered
  /// </summary>
  string Uri { get; }
  /// <summary>
  /// The version of the document being considered. Always increasing
  /// If it did not change, it guarantees that Code is the same.
  /// This might be helpful for caching any pre-computation.
  /// </summary>
  int Version { get; }
  string Code { get; }
  Dafny.Program? Program { get; }
  Diagnostic[] Diagnostics { get; }
  string Extract(Range range);
}
#nullable disable

public delegate List<DafnyCodeAction> ActionSignature(IDafnyCodeActionInput input, Diagnostic diagnostic, Range range);

public static class ErrorRegistry {

#nullable enable
  public static List<ActionSignature>? GetAction(string errorId) {
    return codeActionMap.ContainsKey(errorId) ? new List<ActionSignature> { codeActionMap[errorId] } : null;
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


