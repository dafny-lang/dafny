using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny; 

public class PlatformConstantInjector : IRewriter {

  public PlatformConstantInjector(ErrorReporter reporter) : base(reporter) {
  }

  /// <summary>
  /// TODO
  /// </summary>
  internal override void PreResolve(ModuleDefinition m) {
    foreach(var d in m.TopLevelDecls) {
      
    }
  }
}