using System.Collections.Generic;

namespace Microsoft.Dafny.Compilers; 

public interface IClassWriterAdaptor : IClassWriter {
  public IClassWriter Wrapped { get; }
}