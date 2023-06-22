using System.Collections.Generic;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny.Plugins; 

public abstract class IClassWriterFactory {
  public abstract IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
    List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> /*?*/ superClasses, IToken tok,
    ConcreteSyntaxTree wr);
  
  public abstract IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
    TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr);
  
  public abstract IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr);
  
  public abstract IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr);
}