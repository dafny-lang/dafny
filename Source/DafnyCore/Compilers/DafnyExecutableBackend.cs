using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public abstract class DafnyExecutableBackend : ExecutableBackend {

  protected DafnyExecutableBackend(DafnyOptions options) : base(options)
  {
  }
  
}
