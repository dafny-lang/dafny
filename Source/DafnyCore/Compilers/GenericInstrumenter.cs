using Microsoft.Dafny;

// Some common hooks for instrumenters,
// since the compilation of these program elements tends to be similar
// across the different backends.
public abstract class GenericInstrumenter {
  
  public abstract void BeforeClass(TopLevelDecl cls, ConcreteSyntaxTree wr);
  
  public abstract void BeforeMethod(Method m, ConcreteSyntaxTree wr);
}