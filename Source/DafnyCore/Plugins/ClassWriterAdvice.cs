namespace Microsoft.Dafny.Plugins; 

public abstract class ClassWriterAdvice {

  public abstract IClassWriterFactory WrapClassWriterFactory(IClassWriterFactory factory);
}