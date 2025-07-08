using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class ScopeCloner : DeepModuleSignatureCloner {
  private VisibilityScope scope = null;

  private Dictionary<Declaration, Declaration> reverseMap = new();

  private bool IsInvisibleClone(Declaration d) {
    Contract.Assert(reverseMap.ContainsKey(d));
    return !reverseMap[d].IsVisibleInScope(scope);
  }

  public ScopeCloner(VisibilityScope scope) {
    this.scope = scope;
  }

  private bool RevealedInScope(Declaration d) {
    return d.IsRevealedInScope(scope);
  }

  private bool VisibleInScope(Declaration d) {
    return d.IsVisibleInScope(scope);
  }

  public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, ModuleDefinition newParent, Name name) {
    var basem = base.CloneModuleDefinition(m, newParent, name);

    //Merge signatures for imports which point to the same module
    //This makes the consistency check understand that the same element
    //may be referred to via different qualifications.
    var sigmap = new Dictionary<ModuleDefinition, ModuleSignature>();
    var declmap = new Dictionary<ModuleDefinition, List<AliasModuleDecl>>();
    var vismap = new Dictionary<ModuleDefinition, VisibilityScope>();

    foreach (var top in basem.TopLevelDecls) {
      var import = reverseMap[top] as AliasModuleDecl;
      if (import == null) {
        continue;
      }

      var def = import.Signature.ModuleDef;
      if (def == null) {
        continue;
      }

      if (!declmap.ContainsKey(def)) {
        declmap.Add(def, []);
        sigmap.Add(def, new ModuleSignature());
        vismap.Add(def, new VisibilityScope());
      }

      sigmap[def] = ModuleResolver.MergeSignature(sigmap[def], import.Signature);
      sigmap[def].ModuleDef = def;
      declmap[def].Add((AliasModuleDecl)top);
      if (VisibleInScope(import)) {
        vismap[def].Augment(import.Signature.VisibilityScope);
      }

    }

    foreach (var decls in declmap) {
      sigmap[decls.Key].VisibilityScope = vismap[decls.Key];
      foreach (var decl in decls.Value) {
        decl.Signature = sigmap[decls.Key];
      }
    }

    bool RemovePredicate(TopLevelDecl topLevelDecl) {
      if (topLevelDecl is AliasModuleDecl aliasModuleDecl) {
        var def = aliasModuleDecl.Signature.ModuleDef;
        return def != null && vismap[def].IsEmpty();
      }

      return IsInvisibleClone(topLevelDecl);
    }

    basem.SourceDecls.RemoveAll(RemovePredicate);
    basem.ResolvedPrefixNamedModules.RemoveAll(RemovePredicate);

    basem.TopLevelDecls.OfType<TopLevelDeclWithMembers>().
      ForEach(t => t.Members.RemoveAll(IsInvisibleClone));

    return basem;
  }

  public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition newParent) {
    var based = base.CloneDeclaration(d, newParent);
    if (d is (RevealableTypeDecl or TopLevelDeclWithMembers) and not DefaultClassDecl && !RevealedInScope(d)) {
      var tps = d.TypeArgs.ConvertAll(CloneTypeParam);
      var characteristics = TypeParameter.GetExplicitCharacteristics(d);
      var members = based is TopLevelDeclWithMembers tm ? tm.Members : [];
      // copy the newParent traits only if "d" is already an AbstractTypeDecl and is being export-revealed
      var otd = new AbstractTypeDecl(Origin(d.Origin), d.NameNode.Clone(this), newParent, characteristics, tps,
        [], // omit the newParent traits
        members, CloneAttributes(d.Attributes), d.IsRefining);
      based = otd;
      if (d is ClassLikeDecl { IsReferenceTypeDecl: true } cl) {
        reverseMap.Add(based, cl.NonNullTypeDecl);
        return based;
      }
    }

    reverseMap.Add(based, d);
    return based;

  }

  public override Field CloneField(Field f) {
    if (f is ConstantField { Rhs: not null } cf && !RevealedInScope(f)) {
      // We erase the RHS value. While we do that, we must also make sure the declaration does have a type, so instead of
      // cloning cf.Type, we assume "f" has been resolved and clone cf.Type.NormalizeExpandKeepConstraints().
      return new ConstantField(Origin(cf.Origin), cf.NameNode.Clone(this), null, cf.HasStaticKeyword, cf.IsGhost, cf.IsOpaque, CloneType(cf.Type.NormalizeExpandKeepConstraints()), CloneAttributes(cf.Attributes));
    }
    return base.CloneField(f);
  }

  public override Function CloneFunction(Function f, string newName = null) {
    var basef = base.CloneFunction(f, newName);
    if (basef.ByMethodBody != null) {
      Contract.Assert(!basef.IsGhost); // a function-by-method has .IsGhost == false
      Contract.Assert(basef.Body != null); // a function-by-method has a nonempty .Body
      if (RevealedInScope(f)) {
        // For an "export reveals", use an empty (but not absent) by-method part.
        basef.ByMethodBody = new BlockStmt(basef.ByMethodBody.Origin, []);
      } else {
        // For an "export provides", remove the by-method part altogether.
        basef.ByMethodTok = null;
        basef.ByMethodBody = null;
      }
    }
    if (!RevealedInScope(f)) {
      basef.Body = null;
    }
    return basef;
  }

  public override MethodOrConstructor CloneMethod(MethodOrConstructor m) {
    var basem = base.CloneMethod(m);
    basem.SetBody(null); //exports never reveal method bodies
    return basem;
  }

  public override MemberDecl CloneMember(MemberDecl member, bool isReference) {
    var basem = base.CloneMember(member, isReference);
    reverseMap.Add(basem, member);
    return basem;
  }

}