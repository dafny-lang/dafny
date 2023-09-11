using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public interface IDeclarationOrUsage : INode {
  IToken NameToken { get; }
}

public interface IHasUsages : IDeclarationOrUsage {
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations();
}

/// <summary>
/// A symbol that potential has something to verify
/// </summary>
public interface ICanVerify : ISymbol {
  ModuleDefinition ContainingModule { get; }

  /// <summary>
  /// Return true if this symbol has something to verify.
  /// If true is incorrectly returned, the IDE will allow the user to verify this but it'll pass immediately.
  /// </summary>
  bool ShouldVerify { get; }
}

public static class AstExtensions {

  public static string GetMemberQualification(MemberDecl memberDecl) {
    if (memberDecl.EnclosingClass == null) {
      // If traversing up the AST is already made available after parsing, this branch can be removed.
      return "";
    }
    return memberDecl.EnclosingClass.Name == "_default" ? "" : $"{memberDecl.EnclosingClass.Name}.";
  }

  /// <summary>
  /// Returns a text representation of the given variable.
  /// </summary>
  /// <param name="variable">The variable to get a text representation of.</param>
  /// <returns>The text representation of the variable.</returns>
  public static string AsText(this IVariable variable) {
    var ghost = variable.IsGhost ? "ghost " : "";
    string type;
    try {
      type = variable.Type.ToString();
    } catch (Exception e) {
      type = $"<Internal error: {e.Message}>";
    }
    return $"{ghost}{variable.Name}: {type}";
  }
}

public interface ISymbol : IDeclarationOrUsage {
  DafnySymbolKind Kind { get; }

  string GetDescription(DafnyOptions options);
}

public interface IHasSymbolChildren : ISymbol {
  IEnumerable<ISymbol> ChildSymbols { get; }
}

public static class SymbolExtensions {

  public static ISet<ISymbol> GetSymbolDescendants(ISymbol node) {
    var todo = new Stack<ISymbol>();
    todo.Push(node);
    var result = new HashSet<ISymbol>();
    while (todo.Any()) {
      var current = todo.Pop();
      result.Add(current);
      if (current is IHasSymbolChildren hasChildren) {
        foreach (var child in hasChildren.ChildSymbols) {
          todo.Push(child);
        }
      }
    }
    return result;
  }
}

/// <summary>
/// This is a copy of OmniSharp.Extensions.LanguageServer.Protocol.Models.SymbolKind
/// In the future, we'll include that package in this project, and then this copy can be removed.
/// For now, adding that package reference is not worth its weight.
/// </summary>
public enum DafnySymbolKind {
  File = 1,
  Module = 2,
  Namespace = 3,
  Package = 4,
  Class = 5,
  Method = 6,
  Property = 7,
  Field = 8,
  Constructor = 9,
  Enum = 10,
  Interface = 11,
  Function = 12,
  Variable = 13,
  Constant = 14,
  String = 15,
  Number = 16,
  Boolean = 17,
  Array = 18,
  Object = 19,
  Key = 20,
  Null = 21,
  EnumMember = 22,
  Struct = 23,
  Event = 24,
  Operator = 25,
  TypeParameter = 26,
}