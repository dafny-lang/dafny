namespace Microsoft.Dafny.Plugins; 

// A hook for plugins to customize some of the code generation of other ExecutableBackends.
// The compilation pipeline will apply each ClassWriterAdvice that plugins contribute
// to wrap the default IClassWriterFactory instance with customization.
// This customization can insert extra logic/code generation before, after, or around
// the original IClassWriterFactory, such as adding extra annotations when new classes are declared
// in the target language code.
public abstract class ClassWriterAdvice {
  // TODO: Definitely not the best choice of type name.
  // My Aspect-oriented Programming background is showing,
  // and this will not resonate with any other users.
  // But it's still marginally better than the almost-intentionally-mocking-enterprise-naming-idioms
  // ClassWriterFactoryWrapperFactory :)

  public abstract IClassWriterFactory WrapClassWriterFactory(IClassWriterFactory factory);
}