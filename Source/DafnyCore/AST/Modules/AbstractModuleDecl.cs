using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
/// Used to be called ModuleFacadeDecl -- renamed to be like LiteralModuleDecl, AliasModuleDecl
/// </summary>
public class AbstractModuleDecl : ModuleDecl, ICanFormat {
  public ModuleQualifiedId QId;
  public List<IOrigin> Exports; // list of exports sets
  public ModuleDecl CompileRoot;
  public ModuleSignature OriginalSignature;

  public AbstractModuleDecl(Cloner cloner, AbstractModuleDecl original, ModuleDefinition enclosingModule)
    : base(cloner, original, enclosingModule) {
    Exports = original.Exports;
    QId = new ModuleQualifiedId(cloner, original.QId);
    Opened = original.Opened;
  }

  public AbstractModuleDecl(DafnyOptions options, IOrigin origin, ModuleQualifiedId qid, Name name, Attributes attributes,
    ModuleDefinition enclosingModule, bool opened, List<IOrigin> exports, Guid cloneId)
    : base(options, origin, name, attributes, enclosingModule, cloneId) {
    Contract.Requires(qid != null && qid.Path.Count > 0);
    Contract.Requires(exports != null);

    QId = qid;
    Exports = exports;
    Opened = opened;
  }

  public override bool Opened { get; }

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