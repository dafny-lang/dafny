using Microsoft.Dafny;

// Some common hooks for instrumenters,
// since the compilation of these program elements tends to be similar
// across the different backends.
public abstract class GenericCompilationInstrumenter {

  // <summary>
  // Invoked just before outputting the code for a Dafny class.
  // </summary>
  public virtual void BeforeClass(TopLevelDecl cls, ConcreteSyntaxTree wr) { }

  // <summary>
  // Invoked just before outputting the code for a Dafny method.
  // </summary>
  public virtual void BeforeMethod(MethodOrConstructor m, ConcreteSyntaxTree wr) { }
}