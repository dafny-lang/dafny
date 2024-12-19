using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Represents module X { ... }
/// </summary>
public class LiteralModuleDecl : ModuleDecl, ICanFormat, IHasSymbolChildren {
  public readonly ModuleDefinition ModuleDef;

  [FilledInDuringResolution] public ModuleSignature DefaultExport;  // the default export set of the module.

  private ModuleSignature emptySignature;
  public override ModuleSignature AccessibleSignature(bool ignoreExports) {
    if (ignoreExports) {
      return Signature;
    }
    return this.AccessibleSignature();
  }

  public override bool SingleFileToken => ModuleDef.SingleFileToken;

  public override ModuleSignature AccessibleSignature() {
    if (DefaultExport == null) {
      if (emptySignature == null) {
        emptySignature = new ModuleSignature();
      }
      return emptySignature;
    }
    return DefaultExport;
  }

  public override IEnumerable<INode> Children => new[] { ModuleDef };
  public override IEnumerable<INode> PreResolveChildren => Children;

  public LiteralModuleDecl(Cloner cloner, LiteralModuleDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    var newModuleDefinition = cloner.CloneLiteralModuleDefinition ? cloner.CloneModuleDefinition(original.ModuleDef, parent) : original.ModuleDef;
    ModuleDef = newModuleDefinition;
    DefaultExport = original.DefaultExport;
    BodyStartTok = ModuleDef.BodyStartTok;
  }

  public LiteralModuleDecl(DafnyOptions options, ModuleDefinition module, ModuleDefinition parent, Guid cloneId)
    : base(options, module.Origin, module.NameNode, parent, false, false, cloneId) {
    ModuleDef = module;
    BodyStartTok = module.BodyStartTok;
    module.EnclosingLiteralModuleDecl = this;
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

    Attributes.SetIndents(Attributes, indentBefore, formatter);
    Attributes.SetIndents(ModuleDef.Attributes, indentBefore, formatter);

    foreach (var decl2 in ModuleDef.TopLevelDecls) {
      formatter.SetDeclIndentation(decl2, innerIndent);
    }

    foreach (var decl2 in ModuleDef.PrefixNamedModules) {
      formatter.SetDeclIndentation(decl2.Module, innerIndent);
    }

    return true;
  }

  public ModuleSignature Resolve(ModuleResolver resolver, CompilationData compilation) {
    // The declaration is a literal module, so it has members and such that we need
    // to resolve. First we do refinement transformation. Then we construct the signature
    // of the module. This is the public, externally visible signature. Then we add in
    // everything that the system defines, as well as any "import" (i.e. "opened" modules)
    // directives (currently not supported, but this is where we would do it.) This signature,
    // which is only used while resolving the members of the module is stored in the (basically)
    // global variable moduleInfo. Then the signatures of the module members are resolved, followed
    // by the bodies.
    var module = ModuleDef;

    var errorCount = resolver.reporter.ErrorCount;
    if (module.Implements != null) {
      var md = module.Implements.Target.ResolveTarget(resolver.reporter);
      module.Implements.Target.SetTarget(md); // If module is not found, md is null and an error message has been emitted
    }

    var rewriters = RewriterCollection.GetRewriters(resolver.Reporter, resolver.ProgramResolver.Program);
    foreach (var rewriter in rewriters) {
      rewriter.PreResolve(module);
    }

    Signature = module.RegisterTopLevelDecls(resolver, true);
    Signature.Refines = module.Implements?.Target.Sig;

    var sig = Signature;
    // set up environment
    var preResolveErrorCount = resolver.reporter.ErrorCount;

    resolver.ResolveModuleExport(this, sig);
    var good = module.Resolve(sig, resolver);

    if (good && resolver.reporter.ErrorCount == preResolveErrorCount) {
      // Check that the module export gives a self-contained view of the module.
      resolver.CheckModuleExportConsistency(compilation, module);
    }

    var tempVis = new VisibilityScope();
    tempVis.Augment(sig.VisibilityScope);
    tempVis.Augment(resolver.ProgramResolver.SystemModuleManager.systemNameInfo.VisibilityScope);
    Type.PushScope(tempVis);

    foreach (var rewriter in rewriters) {
      if (!good || resolver.reporter.ErrorCount != preResolveErrorCount) {
        break;
      }

      rewriter.PostResolveIntermediate(module);
    }

    if (good && resolver.reporter.ErrorCount == errorCount) {
      module.SuccessfullyResolved = true;
    }

    Type.PopScope(tempVis);

    if (!good || resolver.reporter.HasErrors) {
      return sig;
    }

    Type.PushScope(tempVis);
    resolver.ComputeIsRecursiveBit(compilation, module, rewriters);
    resolver.FillInDecreasesClauses(module);
    foreach (var iter in module.TopLevelDecls.OfType<IteratorDecl>()) {
      resolver.reporter.Info(MessageSource.Resolver, iter.Tok, Printer.IteratorClassToString(resolver.Reporter.Options, iter));
    }

    foreach (var rewriter in rewriters) {
      rewriter.PostDecreasesResolve(module);
    }

    resolver.FillInAdditionalInformation(module);
    FuelAdjustment.CheckForFuelAdjustments(resolver.reporter, module);

    foreach (var rewriter in rewriters) {
      rewriter.PostResolve(module);
    }

    Type.PopScope(tempVis);
    return sig;
  }

  public void BindModuleNames(ProgramResolver resolver, ModuleBindings parentBindings) {
    Contract.Requires(this != null);
    Contract.Requires(parentBindings != null);

    var bindings = ModuleDef.BindModuleNames(resolver, parentBindings);
    if (!parentBindings.BindName(Name, this, bindings)) {
      parentBindings.TryLookup(Name, out var otherModule);
      resolver.Reporter.Error(MessageSource.Resolver, new NestedOrigin(Tok, otherModule.Tok), "Duplicate module name: {0}", Name);
    }
  }

  public IEnumerable<ISymbol> ChildSymbols => ModuleDef.TopLevelDecls.SelectMany(decl => {
    if (decl is DefaultClassDecl defaultClassDecl) {
      return defaultClassDecl.Members;
    }

    if (decl is ISymbol symbol) {
      return new[] { symbol };
    }

    return Enumerable.Empty<ISymbol>();
  });
}