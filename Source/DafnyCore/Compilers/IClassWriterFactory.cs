using System.Collections.Generic;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny.Plugins; 

// An interface for code generation actions that end up generating target language "classes".
// A higher-level operation like DeclareDatatype will both write the top-level declaration
// of a class and also create a IClassWriter that other logic can use to fill in details like
// constructors, fields, and methods, especially in the more generic SinglePassCompiler base class.
// This interface is used so that plugin have the opportunity to customize this behavior,
// such as inserting additional annotations on the declared classes using IClassWriter.ClassHeaderWriter()
public abstract class IClassWriterFactory {
  public abstract IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
    List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> /*?*/ superClasses, IToken tok,
    ConcreteSyntaxTree wr);
  
  public abstract IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
    TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr);
  
  public abstract IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr);
  
  public abstract IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr);
}