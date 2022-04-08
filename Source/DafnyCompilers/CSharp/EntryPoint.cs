using System.Collections.ObjectModel;
using DafnyInDafny.CSharp;

namespace Microsoft.Dafny.Compilers.SelfHosting.CSharp;

internal class SelfHostingCSharpCompiler : SelfHostingCompiler {
  private readonly DafnyCSharpCompiler compiler = new ();

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetLanguage => "C#";
  public override string TargetExtension => "cs";

  public override string PublicIdProtect(string name) {
    return new CsharpCompiler().PublicIdProtect(name);
  }

  public override bool TextualTargetIsExecutable => false;
  public override bool SupportsInMemoryCompilation => false;

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    compiler.EmitCallToMain(mainMethod, baseName, output);
  }
}
