namespace Microsoft.Dafny;

class AbstractSignatureCloner : ScopeCloner {

  public AbstractSignatureCloner(VisibilityScope scope)
    : base(scope) {
  }

  public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, Name name) {
    var basem = base.CloneModuleDefinition(m, name);
    basem.SourceDecls.RemoveAll(t => t is ModuleExportDecl);
    basem.ResolvedPrefixNamedModules.RemoveAll(t => t is ModuleExportDecl);
    return basem;
  }

  public override BlockStmt CloneMethodBody(Method m) {
    return null;
  }
}