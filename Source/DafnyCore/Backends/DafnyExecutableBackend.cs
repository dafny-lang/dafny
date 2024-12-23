using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using Dafny;

namespace Microsoft.Dafny.Compilers;

public abstract class DafnyExecutableBackend : ExecutableBackend {

  protected virtual bool PreventShadowing => true;
  protected virtual bool CanEmitUncompilableCode => true;
  public override bool SupportsDatatypeWrapperErasure => false;

  protected virtual string InternalFieldPrefix => "_i_";

  protected DafnyWrittenCodeGenerator DafnyCodeGenerator;

  public List<string> ImportedFiles = new();

  protected DafnyExecutableBackend(DafnyOptions options) : base(options) {
  }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    // becomes this.compiler
    return new DafnyCodeGenerator(Options, Reporter, InternalFieldPrefix, PreventShadowing, CanEmitUncompilableCode);
  }

  protected abstract DafnyWrittenCodeGenerator CreateDafnyWrittenCompiler();

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    DafnyCodeGenerator = CreateDafnyWrittenCompiler();
  }

  // Returns a mapping from source files without extension to pathless target file.
  // Values of this dictionary are provided as the second argument to the Compile method
  // Should ensures all values are different
  public virtual Dictionary<string, string> ImportFilesMapping(string dafnyProgramName) {
    Dictionary<string, string> importedFilesMapping = new();
    return importedFilesMapping;
  }

  public IEnumerable<string> ImportFiles(string dafnyProgramName) {
    var result = ImportFilesMapping(dafnyProgramName).Values.ToList();
    result.Sort();
    return result;
  }

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    ProcessTranslationRecords(dafnyProgram, dafnyProgramName, output);
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);

    ((DafnyCodeGenerator)codeGenerator).Start();
    codeGenerator.Compile(dafnyProgram, new ConcreteSyntaxTree());
    var dast = ((DafnyCodeGenerator)codeGenerator).Build();
    DafnyCodeGenerator.Compile(
      (Sequence<DAST.Module>)Sequence<DAST.Module>.FromArray(dast.ToArray()),
      (Sequence<ISequence<Rune>>)Sequence<ISequence<Rune>>.FromArray(
        ImportFiles(dafnyProgramName).Select(fileName =>
          Sequence<Rune>.UnicodeFromString(Path.GetFileName(fileName))).ToArray()
      ), output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    var sourceBuf = new ExprBuffer(null);
    var mainCallHolder = new BuilderSyntaxTree<ExprContainer>(sourceBuf, ((DafnyCodeGenerator)codeGenerator));
    ((DafnyCodeGenerator)codeGenerator).TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), mainCallHolder, mainMethod.Tok, mainMethod);
    var companion = sourceBuf.Finish();
    var hasArguments = mainMethod.Ins.Any();
    var mainMethodName = (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(mainMethod.Name);
    var o = DafnyCodeGenerator.EmitCallToMain(companion, mainMethodName, hasArguments);
    output.Write(o.ToVerbatimString(false));
  }

}
