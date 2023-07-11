using Microsoft.Dafny;

public abstract class GenericInstrumenter {
  
  public abstract void BeforeClass(TopLevelDecl cls, ConcreteSyntaxTree wr);
  
  public abstract void BeforeMethod(Method m, ConcreteSyntaxTree wr);
}