using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public interface IDeclarationOrUsage : INode {
  IToken NameToken { get; }
}

public interface IHasUsages : IDeclarationOrUsage {
  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations();
}

public static class AstExtensions {

  public static string GetMemberQualification(MemberDecl memberDecl) {
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