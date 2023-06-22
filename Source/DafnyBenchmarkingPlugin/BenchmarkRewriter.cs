using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using Type = Microsoft.Dafny.Type;

namespace DafnyBenchmarkingPlugin;

public class JavaBenchmarkClassWriterAdvice : ClassWriterAdvice {
  public override IClassWriterFactory WrapClassWriterFactory(IClassWriterFactory factory) {
    return new JavaBenchmarkClassWriterFactory(factory);
  }
}

public class JavaBenchmarkClassWriterFactory : IClassWriterFactory {
  private readonly IClassWriterFactory wrapped;

  public JavaBenchmarkClassWriterFactory(IClassWriterFactory wrapped) {
    this.wrapped = wrapped;
  }


  public override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
    List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> /*?*/ superClasses, IToken tok,
    ConcreteSyntaxTree wr) {
    
    var wrappedWriter = wrapped.CreateClass(moduleName, name, isExtern, fullPrintName, typeParameters, cls, superClasses,
      tok, wr);
    
    // if (Attributes.Contains(cls.Attributes, "benchmark")) {
    //   wr.WriteLine("@State(...)");
    // }

    return new JavaBenchmarkClassWriter(wrappedWriter);
  }

  public override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters, TopLevelDecl trait, List<Type> superClasses,
    IToken tok, ConcreteSyntaxTree wr) {
    return wrapped.CreateTrait(name, isExtern, typeParameters, trait, superClasses, tok, wr);
  }

  public override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
    return wrapped.DeclareNewtype(nt, wr);
  }

  public override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
    return wrapped.DeclareDatatype(dt, wr);
  }
}

class JavaBenchmarkClassWriter : IClassWriter {

  private readonly IClassWriter wrapped;

  public JavaBenchmarkClassWriter(IClassWriter wrapped) {
    this.wrapped = wrapped;
  }

  public ConcreteSyntaxTree ClassHeaderWriter() {
    return wrapped.ClassHeaderWriter();
  }

  public ConcreteSyntaxTree CreateMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody, out ConcreteSyntaxTree headerWriter) {
    var result = wrapped.CreateMethod(m, typeArgs, createBody, forBodyInheritance, lookasideBody, out headerWriter);
    
    if (Attributes.Contains(m.EnclosingClass.Attributes, "benchmark")) {
      headerWriter.WriteLine("@Benchmark");
    }

    return result;
  }

  public ConcreteSyntaxTree SynthesizeMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance,
    bool lookasideBody) {
    return wrapped.SynthesizeMethod(m, typeArgs, createBody, forBodyInheritance, lookasideBody);
  }

  public ConcreteSyntaxTree CreateFunction(string name, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic,
    bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
    return wrapped.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, forBodyInheritance, lookasideBody);
  }

  public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic,
    bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
    return wrapped.CreateGetter(name, enclosingDecl, resultType, tok, isStatic, isConst, createBody, member, forBodyInheritance);
  }

  public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl member,
    out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
    return wrapped.CreateGetterSetter(name, resultType, tok, createBody, member, out setterWriter, forBodyInheritance);
  }

  public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok,
    string rhs, Field field) {
    wrapped.DeclareField(name, enclosingDecl, isStatic, isConst, type, tok, rhs, field);
  }

  public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
    wrapped.InitializeField(field, instantiatedFieldType, enclosingClass);
  }

  public ConcreteSyntaxTree ErrorWriter() {
    return wrapped.ErrorWriter();
  }

  public void Finish() {
    wrapped.Finish();
  }
}