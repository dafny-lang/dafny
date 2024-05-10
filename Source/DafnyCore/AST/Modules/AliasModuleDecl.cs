using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.CodeAnalysis;

namespace Microsoft.Dafny;

/// <summary>
/// Represents "module name = path;", where name is an identifier and path is a possibly qualified name.
/// </summary>
public class AliasModuleDecl : ModuleDecl, ICanFormat {
  public readonly ModuleQualifiedId TargetQId; // generated by the parser, this is looked up
  public readonly List<IToken> Exports; // list of exports sets
  [FilledInDuringResolution] public bool ShadowsLiteralModule;  // initialized early during Resolution (and used not long after that); true for "import opened A = A" where "A" is a literal module in the same scope

  public AliasModuleDecl(Cloner cloner, AliasModuleDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    if (original.TargetQId != null) { // TODO is this null check necessary?
      TargetQId = new ModuleQualifiedId(cloner, original.TargetQId);

      /*
       * Refinement cloning happens in PreResolver, which is after the ModuleQualifiedId.Root fields are set,
       * so this field must be copied as part of refinement cloning.
       * However, letting refinement cloning set CloneResolvedFields==true causes exceptions for an uninvestigated reason,
       * so we will clone this field even when !CloneResolvedFields.
       */
      TargetQId.Root = original.TargetQId.Root;
    }
    Exports = original.Exports;
  }

  public AliasModuleDecl(DafnyOptions options, RangeToken rangeToken, ModuleQualifiedId path, Name name,
    ModuleDefinition parent, bool opened, List<IToken> exports, Guid cloneId)
    : base(options, rangeToken, name, parent, opened, false, cloneId) {
    Contract.Requires(path != null && path.Path.Count > 0);
    Contract.Requires(exports != null);
    Contract.Requires(exports.Count == 0 || path.Path.Count == 1);
    TargetQId = path;
    Exports = exports;
  }

  public override ModuleDefinition Dereference() { return Signature.ModuleDef; }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    if (OwnedTokens.FirstOrDefault() is { } theToken) {
      formatter.SetOpeningIndentedRegion(theToken, indentBefore);
    }

    return true;
  }

  /// <summary>
  /// If no explicit name is given for an import declaration,
  /// Then we consider this as a reference, not a declaration, from the IDE perspective.
  /// So any further references to the imported module then resolve directly to the module,
  /// Not to this import declaration.
  ///
  /// Code wise, it might be better not to let AliasModuleDecl inherit from Declaration,
  /// since it is not always a declaration. 
  /// </summary>
  public override IToken NameToken =>
    NameNode.StartToken == NameNode.EndToken ? TargetQId.Decl.NameToken : base.NameToken;

  public override IEnumerable<INode> Children => base.Children.Concat(new INode[] { TargetQId });
}