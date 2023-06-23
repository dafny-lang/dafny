using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using Type = Microsoft.Dafny.Type;

namespace DafnyBenchmarkingPlugin;

// TODO: Need to detect which compiler is active so we only conditionally apply this.
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
    
    if (Attributes.Contains(cls.Attributes, "benchmark")) {
      wrappedWriter.ClassHeaderWriter().WriteLine("@org.openjdk.jmh.annotations.State(org.openjdk.jmh.annotations.Scope.Benchmark)");
    }

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

class JavaBenchmarkClassWriter : IClassWriterAdaptor {

  public IClassWriter Wrapped { get; }

  public JavaBenchmarkClassWriter(IClassWriter wrapped) {
    this.Wrapped = wrapped;
  }

  public ConcreteSyntaxTree ClassHeaderWriter() {
    return Wrapped.ClassHeaderWriter();
  }

  public ConcreteSyntaxTree CreateMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody, out ConcreteSyntaxTree headerWriter) {
    var result = Wrapped.CreateMethod(m, typeArgs, createBody, forBodyInheritance, lookasideBody, out headerWriter);
    
    if (Attributes.Contains(m.EnclosingClass.Attributes, "benchmark")) {
      // TODO: Only do this for the default no-arg constructor.
      // TODO: Have a rewriter reject any other constructors?
      if (m is Constructor) {
        // _ctor() needs to be explicitly invoked as usual,
        // and it's convenient (but a hack) to do this by marking it as Setup
        // TODO: Anything other than the "Benchmark" level isn't actually sound,
        // because it's not safe in general to run a Dafny compiled constructor
        // multiple times on the same object.
        // The solution is probably to maintain the benchmark object
        // as a separate object that Setup instantiates every time.
        headerWriter.WriteLine("@org.openjdk.jmh.annotations.Setup(org.openjdk.jmh.annotations.Level.Iteration)");  
      } else {
        headerWriter.WriteLine("@org.openjdk.jmh.annotations.Benchmark");  
      }
    }

    return result;
  }

  public ConcreteSyntaxTree SynthesizeMethod(Method m, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance,
    bool lookasideBody) {
    return Wrapped.SynthesizeMethod(m, typeArgs, createBody, forBodyInheritance, lookasideBody);
  }

  public ConcreteSyntaxTree CreateFunction(string name, List<SinglePassCompiler.TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic,
    bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
    return Wrapped.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, forBodyInheritance, lookasideBody);
  }

  public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic,
    bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
    return Wrapped.CreateGetter(name, enclosingDecl, resultType, tok, isStatic, isConst, createBody, member, forBodyInheritance);
  }

  public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl member,
    out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
    return Wrapped.CreateGetterSetter(name, resultType, tok, createBody, member, out setterWriter, forBodyInheritance);
  }

  public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok,
    string rhs, Field field) {
    Wrapped.DeclareField(name, enclosingDecl, isStatic, isConst, type, tok, rhs, field);
  }

  public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
    Wrapped.InitializeField(field, instantiatedFieldType, enclosingClass);
  }

  public ConcreteSyntaxTree ErrorWriter() {
    return Wrapped.ErrorWriter();
  }

  public void Finish() {
    Wrapped.Finish();
  }
}