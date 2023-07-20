using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Dafny;

namespace Microsoft.Dafny.Compilers;

public abstract class DafnyExecutableBackend : ExecutableBackend {

  protected DafnyWrittenCompiler dafnyCompiler;

  protected DafnyExecutableBackend(DafnyOptions options) : base(options) {
  }

  protected override SinglePassCompiler CreateCompiler() {
    // becomes this.compiler
    return new DafnyCompiler(Options, Reporter);
  }

  protected abstract DafnyWrittenCompiler CreateDafnyWrittenCompiler();

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    dafnyCompiler = CreateDafnyWrittenCompiler();
  }

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    ((DafnyCompiler)compiler).Start();
    compiler.Compile(dafnyProgram, new ConcreteSyntaxTree());
    var dast = ((DafnyCompiler)compiler).Build();
    var o = dafnyCompiler.Compile((Sequence<DAST.Module>)Sequence<DAST.Module>.FromArray(dast.ToArray()));
    output.Write(o.ToVerbatimString(false));
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    var o = dafnyCompiler.EmitCallToMain(mainMethod.FullSanitizedName);
    output.Write(o.ToVerbatimString(false));
  }

}
