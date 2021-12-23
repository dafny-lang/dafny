using System;
using System.CodeDom.Compiler;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Collections.Generic;
using System.IO.Pipelines;
using System.Linq;
using System.Reactive.Concurrency;
using System.Text;
using System.Text.Json;
using System.Threading;
using Microsoft.CodeAnalysis;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.JsonRpc.Client;
using OmniSharp.Extensions.JsonRpc.Serialization;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {    
  class AlwaysOutputFilter : IOutputFilter { public bool ShouldOutput(object value) => true; }

  [TestClass]
  public class ShutdownTest {
    
    [TestMethod]
    public async Task LanguageServerStaysAliveIfNoParentIdIsProvided() {
      var process = await StartLanguageServerRunnerProcess();

      var initializeMessage = await GetLspInitializeMessage(null);
      Thread.Sleep(1000);
      await process.StandardInput.WriteAsync(initializeMessage);
      
      var languageServerProcessId = await process.StandardOutput.ReadToEndAsync();
      var error = await process.StandardError.ReadToEndAsync();
      var didExit = process.WaitForExit(-1);
      Assert.IsTrue(didExit);
      Assert.IsNotNull(languageServerProcessId, error);
      try {
        Thread.Sleep(1000);
        var languageServer = Process.GetProcessById(int.Parse(languageServerProcessId));
        languageServer.Kill();
      } catch (ArgumentException e) {
        Assert.Fail("Language server should not have killed itself if it doesn't know the parent.");
      }
    }

    [TestMethod]
    public async Task LanguageServerShutsDownIfParentDies() {
      var process = await StartLanguageServerRunnerProcess();
      
      var initializeMessage = await GetLspInitializeMessage(process.Id);
      
      var languageServerProcessId = await process.StandardOutput.ReadToEndAsync();
      var error = await process.StandardError.ReadToEndAsync();
      var didExit = process.WaitForExit(-1);
      Assert.IsTrue(didExit);
      Assert.IsTrue(string.IsNullOrEmpty(error), error);

      Assert.IsNotNull(languageServerProcessId, error);
      
      Thread.Sleep(1000);
      await process.StandardInput.WriteAsync(initializeMessage);
      try {
        Thread.Sleep(1000);
        var languageServer = Process.GetProcessById(int.Parse(languageServerProcessId));
        languageServer.Kill();
        Assert.Fail("Language server should have killed itself if the parent is gone.");
      } catch (ArgumentException e) {
        // Language server process is not running, pass the test.
      }
    }

    private static async Task<Process> StartLanguageServerRunnerProcess()
    {
      var languageServerBinary = "/Users/rwillems/Documents/SourceCode/dafny/Binaries/DafnyLanguageServer";
      var languageServerRunnerPath = await CreateDotNetDllThatStartsGivenFilepath(languageServerBinary);

      var processInfo = new ProcessStartInfo("dotnet", languageServerRunnerPath)
      {
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        RedirectStandardInput = true,
        UseShellExecute = false
      };
      return Process.Start(processInfo)!;
    }

    private static async Task<string> GetLspInitializeMessage(int? processId)
    {
      var buffer = new MemoryStream();
      OutputHandler outputHandler = new OutputHandler(PipeWriter.Create(buffer), new JsonRpcSerializer(),
        new List<IOutputFilter> { new AlwaysOutputFilter() },
        TaskPoolScheduler.Default, null);
      outputHandler.Send(new OutgoingRequest {
        Id = 1,
        Method = "initialize",
        Params = new InitializeParams
        {
          ProcessId = processId,
          ClientInfo = new ClientInfo(),
          Capabilities = new ClientCapabilities(),
        }
      });
      await outputHandler.StopAsync();
      return Encoding.ASCII.GetString(buffer.ToArray());
    }

    private static async Task<string> CreateDotNetDllThatStartsGivenFilepath(string filePathToStart)
    {
      var code = @$"using System;
using System.Diagnostics;

public class Foo {{
  public static int Main(string[] args) {{
    var processInfo = new ProcessStartInfo(""{filePathToStart}"") {{
      // Prevents keeping stdio open after the outer process closes. 
      RedirectStandardOutput = true,
      RedirectStandardError = true,
      UseShellExecute = false
    }};
    using var process = Process.Start(processInfo);
    Console.Out.WriteLine(process.Id);
    return 0;
  }}
}}";
      var temp = Path.GetTempFileName();
      var compilation = CSharpCompilation.Create("tempAssembly");
      var standardLibraries = new List<string>()
      {
        "System.Runtime",
        "System.Console",
        "System.Diagnostics.Process",
        "System.ComponentModel.Primitives"
      };
      compilation = compilation.AddReferences(standardLibraries.Select(fileName =>
        MetadataReference.CreateFromFile(Assembly.Load(fileName).Location)));
      compilation = compilation.WithOptions(new CSharpCompilationOptions(OutputKind.ConsoleApplication))
        .AddReferences(
          MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location),
          MetadataReference.CreateFromFile(Assembly.Load("mscorlib").Location));
      var syntaxTree = CSharpSyntaxTree.ParseText(code);
      compilation = compilation.AddSyntaxTrees(syntaxTree);
      var assemblyPath = temp + ".dll";
      var result = compilation.Emit(assemblyPath);

      var configuration = JsonSerializer.Serialize(
        new
        {
          runtimeOptions = new
          {
            tfm = "net5.0",
            framework = new
            {
              name = "Microsoft.NETCore.App",
              version = "5.0.0",
              rollForward = "LatestMinor"
            }
          }
        }, new JsonSerializerOptions() { WriteIndented = true });
      await File.WriteAllTextAsync(temp + ".runtimeconfig.json", configuration + Environment.NewLine);

      Assert.IsTrue(result.Success, string.Join("\n", result.Diagnostics.Select(d => d.ToString())));
      return assemblyPath;
    }
  }
}