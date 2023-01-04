using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public abstract class PluginsTestBase : ClientBasedLanguageServerTest {
  protected string LibraryPath;

  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends a Rewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  private static string GetLibrary(string assemblyName) {
    var assembly = Assembly.GetExecutingAssembly();
    string[] names = assembly.GetManifestResourceNames();
    Stream codeStream = assembly.GetManifestResourceStream($"Microsoft.Dafny.LanguageServer.IntegrationTest._plugins.{assemblyName}.cs");
    Assert.IsNotNull(codeStream);
    string code = new StreamReader(codeStream).ReadToEnd();

    var temp = Path.GetTempFileName();
    var compilation = CSharpCompilation.Create(assemblyName);
    var standardLibraries = new List<string>()
    {
      // Just referencing DafnyCore is normally enough in a plugin project,
      // since the build will include transitive dependencies as well,
      // but here we have to explicitly enumerate every dependency.
      // That means DafnyCore is the best reference since it directly contains
      // all the Microsoft.Dafny elements.
      "DafnyCore",
      "System",
      "netstandard",
      "OmniSharp.Extensions.LanguageServer",
      "OmniSharp.Extensions.LanguageProtocol",
      "System.Console",
      "DafnyLanguageServer",
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

  protected abstract string LibraryName { get; }

  protected abstract string[] CommandLineArgument { get; }

  public override Task SetUp(Action<DafnyOptions> modifyOptions) {
    LibraryPath = GetLibrary(LibraryName);
    void ModifyOptions(DafnyOptions options) {
      options.Set(CommonOptionBag.Plugin, CommandLineArgument.ToList());
      modifyOptions?.Invoke(options);
    }
    return base.SetUp(ModifyOptions);
  }
}
