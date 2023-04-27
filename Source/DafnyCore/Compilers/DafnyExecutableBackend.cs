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
  
  protected override SinglePassCompiler CreateCompiler() {
    return new DafnyCompiler(Options, Reporter);
  }
  
  protected abstract DafnyWrittenCompiler CreateDafnyWrittenCompiler();
  
  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
    var dast = ((DafnyCompiler) compiler).DafnyAST;
    
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
  }
  
}
