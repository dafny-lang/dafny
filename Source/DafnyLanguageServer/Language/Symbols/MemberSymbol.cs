namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class MemberSymbol : Symbol {
    /// <summary>
    /// Gets the name of the enclosing class (if any). It will return <c>null</c> if
    /// there's no enclosing class or the member is part of the default class.
    /// </summary>
    public string? EnclosingTypeName {
      get {
        var typeName = (Scope as TypeWithMembersSymbolBase)?.Name;
        return typeName == "_default" ? null : typeName;
      }
    }

    /// <summary>
    /// Gets the type prefix (Typename.} of this member or an empty string if
    /// the member is part of the default class.
    /// </summary>
    public string TypePrefix {
      get {
        var className = EnclosingTypeName;
        return className == null ? string.Empty : $"{className}.";
      }
    }

    public MemberSymbol(ISymbol? scope, MemberDecl memberDeclaration) : base(scope, memberDeclaration.Name) {
    }
  }
}
