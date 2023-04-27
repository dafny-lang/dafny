using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public abstract class DafnyExecutableBackend : ExecutableBackend {

  protected DafnyWrittenCompiler dafnyCompiler;
  
  protected DafnyExecutableBackend(DafnyOptions options) : base(options)
  {
  }
  
  protected override SinglePassCompiler CreateCompiler() {
    return new DafnyCompiler(Options, Reporter);
  }
  
  protected abstract DafnyWrittenCompiler CreateDafnyWrittenCompiler();
  
  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    dafnyCompiler = CreateDafnyWrittenCompiler();
  }
  
  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
    output.Clear();
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
    var dast = ((DafnyCompiler) compiler).DafnyAST;
    var o = dafnyCompiler.Compile(dast);
    callToMainTree.Clear();
    callToMainTree.Write(o.ToVerbatimString(false));
  }
  
}
