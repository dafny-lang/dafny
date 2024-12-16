using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.AccessControl;

namespace Microsoft.Dafny;

/// <summary>
/// Represents the exports of a module.
/// </summary>
public class ModuleExportDecl : ModuleDecl, ICanFormat {
  public readonly bool IsDefault;
  public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
  public List<IOrigin> Extends; // list of exports that are extended
  [FilledInDuringResolution] public readonly List<ModuleExportDecl> ExtendDecls = new();
  public bool RevealAll; // only kept for initial rewriting, then discarded
  public bool ProvideAll;
  public override IEnumerable<INode> Children => Exports;
  public override IEnumerable<INode> PreResolveChildren => Exports;

  public readonly VisibilityScope ThisScope;

  public ModuleDefinition EffectiveModule = null;

  public ModuleExportDecl(Cloner cloner, ModuleExportDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    Exports = original.Exports.Select(s => new ExportSignature(cloner, s)).ToList();
    Extends = original.Extends.Select(cloner.Origin).ToList();
    ProvideAll = original.ProvideAll;
    RevealAll = original.RevealAll;
    IsRefining = original.IsRefining;
    IsDefault = original.IsDefault;
    ThisScope = new VisibilityScope(FullSanitizedName);
    SetupDefaultSignature();
  }

  public ModuleExportDecl(DafnyOptions options, IOrigin rangeOrigin, Name name, ModuleDefinition parent,
    List<ExportSignature> exports, List<IOrigin> extends,
    bool provideAll, bool revealAll, bool isDefault, bool isRefining, Guid cloneId)
    : base(options, rangeOrigin, name, parent, false, isRefining, cloneId) {
    Contract.Requires(exports != null);
    IsDefault = isDefault;
    Exports = exports;
    Extends = extends;
    ProvideAll = provideAll;
    RevealAll = revealAll;
    ThisScope = new VisibilityScope(this.FullSanitizedName);
    SetupDefaultSignature();
  }

  public void SetupDefaultSignature() {
    Contract.Requires(this.Signature == null);
    var sig = new ModuleSignature();
    sig.ModuleDef = this.EnclosingModuleDefinition;
    sig.IsAbstract = this.EnclosingModuleDefinition.ModuleKind == ModuleKindEnum.Abstract;
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

  public override string GetTriviaContainingDocstring() {
    if (GetStartTriviaDocstring(out var triviaFound)) {
      return triviaFound;
    }

    var tentativeTrivia = "";
    if (Tok.pos < EndToken.pos) {
      tentativeTrivia = (Tok.TrailingTrivia + Tok.Next.LeadingTrivia).Trim();
    } else {
      tentativeTrivia = Tok.TrailingTrivia.Trim();
    }
    if (tentativeTrivia != "") {
      return tentativeTrivia;
    }

    tentativeTrivia = EndToken.TrailingTrivia.Trim();
    if (tentativeTrivia != "") {
      return tentativeTrivia;
    }

    return null;
  }
}