namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class MemberSymbol : Symbol {
    /// <summary>
    /// Gets the name of the enclosing class (if any). It will return <c>null</c> if
    /// there's no enclosing class or the member is part of the default class.
    /// </summary>
    public string? EnclosingClassName {
      get {
        var className = (Scope as ClassSymbol)?.Name;
        return className == "_default" ? null : className;
      }
    }

    /// <summary>
    /// Gets the class prefix (Classname.} of this member or an empty string if
    /// the member is part of the default class.
    /// </summary>
    public string ClassPrefix {
      get {
        var className = EnclosingClassName;
        return className == null ? string.Empty : $"{className}.";
      }
    }

    public MemberSymbol(ISymbol? scope, MemberDecl memberDeclaration) : base(scope, memberDeclaration.Name) {
    }
  }
}
