using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public class VerifiedJavaBackend : JavaBackend {

  public override string TargetId => "vjava";
  
  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {

    CodeGenerator.Compile(dafnyProgram, output);
  }
  
  protected override CodeGenerator CreateCodeGenerator() {
    return new VerifiedJavaCodeGenerator();
  }
  
  class VerifiedJavaCodeGenerator : CodeGenerator {
    public string ModuleSeparator { get; }
    public CoverageInstrumenter Coverage { get; }
    public IReadOnlySet<Feature> UnsupportedFeatures { get; }
    public bool SupportsDatatypeWrapperErasure { get; }

    public void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
      var grammar = new JavaGrammar(dafnyProgram.GetStartOfFirstFileToken().Uri).GetFinalGrammar();
      var fileModuleDefinition = new FileModuleDefinition(Token.NoToken) {
        
      };
      fileModuleDefinition.SourceDecls.AddRange(
        dafnyProgram.DefaultModuleDef.SourceDecls.Where(td => !td.IsExtern(dafnyProgram.Options)));
      var outputStringWriter = new StringWriter();
      grammar.ToPrinter().Print(fileModuleDefinition)!.Render(outputStringWriter);
      output.Write(outputStringWriter.ToString());
    }

    public string PublicIdProtect(string name) {
      throw new NotImplementedException();
    }

    public void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    }
  }

  public VerifiedJavaBackend(DafnyOptions options) : base(options) {
  }
}
