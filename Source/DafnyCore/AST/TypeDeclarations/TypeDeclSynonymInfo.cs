using System.Collections.Generic;

namespace Microsoft.Dafny;

public class TypeDeclSynonymInfo {
  public readonly InternalTypeSynonymDecl SelfSynonymDecl;

  public TypeDeclSynonymInfo(TopLevelDecl d) {
    var thisType = UserDefinedType.FromTopLevelDecl(d.Tok, d);
    SelfSynonymDecl = new InternalTypeSynonymDecl(d.Origin, d.NameNode, TypeParameter.GetExplicitCharacteristics(d),
      d.TypeArgs, d.EnclosingModuleDefinition, thisType, d.Attributes);
    SelfSynonymDecl.InheritVisibility(d, false);
  }

  public UserDefinedType SelfSynonym(List<Type> args, Expression /*?*/ namePath = null) {
    return new UserDefinedType(SelfSynonymDecl.Tok, SelfSynonymDecl.Name, SelfSynonymDecl, args, namePath);
  }
}