namespace Microsoft.Dafny.Plugins; 

// TODO: Definitely not the best choice of name.
// My Aspect-oriented Programming background is showing,
// and this will not resonate with any other users.
// But it's still marginally better than the almost-intentionally-mocking-enterprise-naming-idioms
// ClassWriterFactoryWrapperFactory :)
public abstract class ClassWriterAdvice {

  public abstract IClassWriterFactory WrapClassWriterFactory(IClassWriterFactory factory);
}