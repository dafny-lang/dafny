using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Represents the exports of a module.
/// </summary>
public class ModuleExportDecl : ModuleDecl, ICanFormat {
  public bool IsDefault;
  public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
  public List<IOrigin> Extends; // list of exports that are extended
  [FilledInDuringResolution] public List<ModuleExportDecl> ExtendDecls = [];
  public bool RevealAll; // only kept for initial rewriting, then discarded
  public bool ProvideAll;
  public override IEnumerable<INode> Children => Exports;
  public override IEnumerable<INode> PreResolveChildren => Exports;

  public VisibilityScope ThisScope;

  public ModuleDefinition EffectiveModule = null;

  public ModuleExportDecl(Cloner cloner, ModuleExportDecl original, ModuleDefinition enclosingModule)
    : base(cloner, original, enclosingModule) {
    Exports = original.Exports.Select(s => new ExportSignature(cloner, s)).ToList();
    Extends = original.Extends.Select(cloner.Origin).ToList();
    ProvideAll = original.ProvideAll;
    RevealAll = original.RevealAll;
    IsRefining = original.IsRefining;
    IsDefault = original.IsDefault;
    ThisScope = new VisibilityScope(FullSanitizedName);
    SetupDefaultSignature();
  }

  public override bool IsRefining { get; }

  public ModuleExportDecl(DafnyOptions options, IOrigin origin, Name name, Attributes attributes, ModuleDefinition enclosingModule,
    List<ExportSignature> exports, List<IOrigin> extends,
    bool provideAll, bool revealAll, bool isDefault, bool isRefining, Guid cloneId)
    : base(options, origin, name, attributes, enclosingModule, cloneId) {
    Contract.Requires(exports != null);
    IsDefault = isDefault;
    Exports = exports;
    Extends = extends;
    ProvideAll = provideAll;
    IsRefining = isRefining;
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
    if (NameNode.EndToken.pos < EndToken.pos) {
      tentativeTrivia = (NameNode.EndToken.TrailingTrivia + NameNode.EndToken.Next?.LeadingTrivia).Trim();
    } else {
      tentativeTrivia = NameNode.EndToken.TrailingTrivia.Trim();
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