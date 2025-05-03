using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny; 

public class ProtocolDetector(ModuleResolver resolver) : ResolverPass(resolver) {
  public void Check(List<TopLevelDecl> declarations) {
    foreach (var decl in declarations.Where(decl => decl is ModuleDecl or IteratorDecl or ClassDecl or TraitDecl)) {
      ReportError(decl, "protocol DSL does not allow this kind of declaration");
    }
  }
}