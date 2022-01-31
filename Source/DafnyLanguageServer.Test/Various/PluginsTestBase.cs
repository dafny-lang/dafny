using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public abstract class PluginsTestBase : DafnyLanguageServerTestBase {
  protected ILanguageClient Client;
  protected DiagnosticsReceiver DiagnosticReceiver;
  protected string LibraryPath;

  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends a Rewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  private string GetLibrary(string code) {
    var temp = Path.GetTempFileName();
    var compilation = CSharpCompilation.Create("tempAssembly");
    var standardLibraries = new List<string>()
    {
      "DafnyPipeline",
      "System.Runtime",
      "Boogie.Core",
      "System.Collections"
    };
    compilation = compilation.AddReferences(standardLibraries.Select(fileName =>
        MetadataReference.CreateFromFile(Assembly.Load((string)fileName).Location)))
      .AddReferences(
        MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location))
      .WithOptions(
        new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
      );
    var syntaxTree = CSharpSyntaxTree.ParseText(code);
    compilation = compilation.AddSyntaxTrees(syntaxTree);
    var assemblyPath = $"{temp}.dll";
    var result = compilation.Emit(assemblyPath);

    Assert.IsTrue(result.Success, string.Join("\n", result.Diagnostics.Select(d => d.ToString())));
    return assemblyPath;
  }

  protected abstract string GetLibraryCode();

  protected abstract string[] GetCommandLineArgument();

  public async Task SetUpPlugin() {
    DiagnosticReceiver = new();
    LibraryPath = GetLibrary(GetLibraryCode());
    Client = await InitializeClient(options => options.OnPublishDiagnostics(DiagnosticReceiver.NotificationReceived));
  }


  protected override IConfiguration CreateConfiguration() {
    return new ConfigurationBuilder().AddCommandLine(GetCommandLineArgument()).Build();
  }
}