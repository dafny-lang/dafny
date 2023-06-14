using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Security.AccessControl;

namespace Microsoft.Dafny;

/// <summary>
/// Represents the exports of a module.
/// </summary>
public class ModuleExportDecl : ModuleDecl, ICanFormat {
  public readonly bool IsDefault;
  public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
  public List<IToken> Extends; // list of exports that are extended
  [FilledInDuringResolution] public readonly List<ModuleExportDecl> ExtendDecls = new List<ModuleExportDecl>();
  [FilledInDuringResolution] public readonly HashSet<Tuple<Declaration, bool>> ExportDecls = new HashSet<Tuple<Declaration, bool>>();
  public bool RevealAll; // only kept for initial rewriting, then discarded
  public bool ProvideAll;
  public override IEnumerable<Node> Children => Exports;
  public override IEnumerable<Node> PreResolveChildren => Exports;

  public readonly VisibilityScope ThisScope;

  public ModuleDefinition EffectiveModule = null;

  public ModuleExportDecl(Cloner cloner, ModuleExportDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    Exports = original.Exports;
    Extends = original.Extends;
    ProvideAll = original.ProvideAll;
    RevealAll = original.RevealAll;
    IsRefining = original.IsRefining;
    ThisScope = new VisibilityScope(FullSanitizedName);
  }

  public ModuleExportDecl(RangeToken rangeToken, Name name, ModuleDefinition parent,
    List<ExportSignature> exports, List<IToken> extends,
    bool provideAll, bool revealAll, bool isDefault, bool isRefining, Guid cloneId)
    : base(rangeToken, name, parent, false, isRefining, cloneId) {
    Contract.Requires(exports != null);
    IsDefault = isDefault;
    Exports = exports;
    Extends = extends;
    ProvideAll = provideAll;
    RevealAll = revealAll;
    ThisScope = new VisibilityScope(this.FullSanitizedName);
  }

  public void SetupDefaultSignature() {
    Contract.Requires(this.Signature == null);
    var sig = new ModuleSignature();
    sig.ModuleDef = this.EnclosingModuleDefinition;
    sig.IsAbstract = this.EnclosingModuleDefinition.IsAbstract;
    sig.VisibilityScope = new VisibilityScope();
    sig.VisibilityScope.Augment(ThisScope);
    this.Signature = sig;
  }

  public override object Dereference() { return this; }
  public override bool CanBeExported() {
    return false;
  }

  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    var innerIndent = indentBefore + formatter.SpaceTab;
    var revealExportIndent = innerIndent + formatter.SpaceTab;
    var commaIndent = innerIndent;
    foreach (var token in OwnedTokens) {
      switch (token.val) {
        case "export": {
            formatter.SetOpeningIndentedRegion(token, indentBefore);
            break;
          }
        case "extends":
        case "reveals":
        case "provides": {
            if (TokenNewIndentCollector.IsFollowedByNewline(token)) {
              formatter.SetOpeningIndentedRegion(token, innerIndent);
              revealExportIndent = innerIndent + formatter.SpaceTab;
              commaIndent = innerIndent + formatter.SpaceTab;
            } else {
              formatter.SetAlign(innerIndent, token, out revealExportIndent, out commaIndent);
            }

            break;
          }
        case ",": {
            formatter.SetIndentations(token, above: revealExportIndent, inline: commaIndent, below: revealExportIndent);
            break;
          }
      }
    }

    return true;
  }

  protected override string GetTriviaContainingDocstring() {
    if (Tok.TrailingTrivia.Trim() != "") {
      return Tok.TrailingTrivia;
    }

    return GetTriviaContainingDocstringFromStartTokenOrNull();
  }
}