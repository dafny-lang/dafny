using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Represents module X { ... }
/// </summary>
public class LiteralModuleDecl : ModuleDecl, ICanFormat {
  public readonly ModuleDefinition ModuleDef;

  [FilledInDuringResolution] public ModuleSignature DefaultExport;  // the default export set of the module.

  private ModuleSignature emptySignature;
  public override ModuleSignature AccessibleSignature(bool ignoreExports) {
    if (ignoreExports) {
      return Signature;
    }
    return this.AccessibleSignature();
  }
  public override ModuleSignature AccessibleSignature() {
    if (DefaultExport == null) {
      if (emptySignature == null) {
        emptySignature = new ModuleSignature();
      }
      return emptySignature;
    }
    return DefaultExport;
  }

  public override IEnumerable<Node> Children => new[] { ModuleDef };
  public override IEnumerable<Node> PreResolveChildren => Children;

  public LiteralModuleDecl(ModuleDefinition module, ModuleDefinition parent)
    : base(module.RangeToken, module.NameNode, parent, false, false) {
    ModuleDef = module;
    BodyStartTok = module.BodyStartTok;
    TokenWithTrailingDocString = module.TokenWithTrailingDocString;
  }

  public override object Dereference() { return ModuleDef; }
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var innerIndent = indentBefore + formatter.SpaceTab;
    var allTokens = ModuleDef.OwnedTokens.ToList();
    if (allTokens.Any()) {
      formatter.SetOpeningIndentedRegion(allTokens[0], indentBefore);
    }

    foreach (var token in allTokens) {
      switch (token.val) {
        case "abstract":
        case "module": {
            break;
          }
        case "{": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, indentBefore);
            } else {
              formatter.SetAlign(indentBefore, token, out innerIndent, out _);
            }

            break;
          }
        case "}": {
            formatter.SetClosingIndentedRegionAligned(token, innerIndent, indentBefore);
            break;
          }
      }
    }

    foreach (var decl2 in ModuleDef.TopLevelDecls) {
      formatter.SetDeclIndentation(decl2, innerIndent);
    }

    foreach (var decl2 in ModuleDef.PrefixNamedModules) {
      formatter.SetDeclIndentation(decl2.Item2, innerIndent);
    }

    return true;
  }
}