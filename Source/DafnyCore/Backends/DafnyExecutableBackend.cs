using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using Dafny;

namespace Microsoft.Dafny.Compilers;

public abstract class DafnyExecutableBackend : ExecutableBackend {

  protected virtual bool PreventShadowing => true;
  protected virtual bool CanEmitUncompilableCode => true;

  protected DafnyWrittenCodeGenerator DafnyCodeGenerator;

  protected DafnyExecutableBackend(DafnyOptions options) : base(options) {
  }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    // becomes this.compiler
    return new DafnyCodeGenerator(Options, Reporter, PreventShadowing, CanEmitUncompilableCode);
  }

  protected abstract DafnyWrittenCodeGenerator CreateDafnyWrittenCompiler();

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    DafnyCodeGenerator = CreateDafnyWrittenCompiler();
  }

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);
    ((DafnyCodeGenerator)codeGenerator).Start();
    codeGenerator.Compile(dafnyProgram, new ConcreteSyntaxTree());
    var dast = ((DafnyCodeGenerator)codeGenerator).Build();
    var o = DafnyCodeGenerator.Compile((Sequence<DAST.Module>)Sequence<DAST.Module>.FromArray(dast.ToArray()));
    output.Write(o.ToVerbatimString(false));
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    var o = DafnyCodeGenerator.EmitCallToMain(mainMethod.FullSanitizedName);
    output.Write(o.ToVerbatimString(false));
  }

}
