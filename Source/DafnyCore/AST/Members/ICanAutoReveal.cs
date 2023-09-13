namespace Microsoft.Dafny; 

public interface ICanAutoRevealDependencies {
  public void AutoRevealDependencies(AutoRevealFunctionDependencies Rewriter, DafnyOptions Options, ErrorReporter Reporter);
}