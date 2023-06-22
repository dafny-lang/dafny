using System.Collections.Generic;

namespace Microsoft.Dafny.Compilers; 

public interface IClassWriter {
  ConcreteSyntaxTree /*?*/ ClassHeaderWriter();
  ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody, out ConcreteSyntaxTree headerWriter);
  ConcreteSyntaxTree/*?*/ SynthesizeMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody);
  ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody,
    MemberDecl member, bool forBodyInheritance, bool lookasideBody);
  ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance);  // returns null iff !createBody
  ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance);  // if createBody, then result and setterWriter are non-null, else both are null
  void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field/*?*/ field);
  /// <summary>
  /// InitializeField is called for inherited fields. It is in lieu of calling DeclareField and is called only if
  /// ClassesRedeclareInheritedFields==false for the compiler.
  /// </summary>
  void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass);
  ConcreteSyntaxTree/*?*/ ErrorWriter();
  void Finish();
}