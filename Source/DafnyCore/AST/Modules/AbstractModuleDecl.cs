using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
/// Used to be called ModuleFacadeDecl -- renamed to be like LiteralModuleDecl, AliasModuleDecl
/// </summary>
public class AbstractModuleDecl : ModuleDecl, ICanFormat {
  public readonly ModuleQualifiedId QId;
  public readonly List<IOrigin> Exports; // list of exports sets
  public ModuleDecl CompileRoot;
  public ModuleSignature OriginalSignature;

  public AbstractModuleDecl(Cloner cloner, AbstractModuleDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    Exports = original.Exports;
    QId = new ModuleQualifiedId(cloner, original.QId);
  }

  public AbstractModuleDecl(DafnyOptions options, IOrigin rangeOrigin, ModuleQualifiedId qid, Name name,
    ModuleDefinition parent, bool opened, List<IOrigin> exports, Guid cloneId)
    : base(options, rangeOrigin, name, parent, opened, false, cloneId) {
    Contract.Requires(qid != null && qid.Path.Count > 0);
    Contract.Requires(exports != null);

    QId = qid;
    Exports = exports;
  }

  public override object Dereference() { return this; }
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "import": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case ":": {
            break;
          }
      }
    }

    return true;
  }
}