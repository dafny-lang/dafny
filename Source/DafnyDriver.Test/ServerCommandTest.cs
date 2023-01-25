using System.Diagnostics;
using System.IO.Pipelines;
using System.Reactive.Concurrency;
using System.Reflection;
using System.Text;
using Microsoft.Extensions.Logging.Abstractions;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.JsonRpc.Client;
using OmniSharp.Extensions.JsonRpc.Serialization;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace DafnyDriver.Test;

public class ServerCommandTest {
  [Fact]
  public async Task InitialisationWorks() {

    var process = StartLanguageServerRunnerProcess();
    var initializeMessage = await GetLspInitializeMessage(process.Id);
    await process.StandardInput.WriteAsync(initializeMessage);

    var initializedResponseFirstLine = await process.StandardOutput.ReadLineAsync();
    Assert.False(string.IsNullOrEmpty(initializedResponseFirstLine));
    process.Kill();
    await process.WaitForExitAsync();
  }

  private Process StartLanguageServerRunnerProcess() {
    var dafnyBinary = Path.Join(Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location), "DafnyDriver.dll");

    var processInfo = new ProcessStartInfo("dotnet", dafnyBinary + " server") {
      RedirectStandardOutput = true,
      RedirectStandardError = true,
      RedirectStandardInput = true,
      UseShellExecute = false
    };

    return Process.Start(processInfo)!;
  }

  private static async Task<string> GetLspInitializeMessage(int? processId) {
    var buffer = new MemoryStream();
    OutputHandler outputHandler = new OutputHandler(PipeWriter.Create(buffer), new JsonRpcSerializer(),
      new List<IOutputFilter> { new AlwaysOutputFilter() },
      TaskPoolScheduler.Default, new NullLogger<OutputHandler>());
    outputHandler.Send(new OutgoingRequest {
      Id = 1,
      Method = "initialize",
      Params = new InitializeParams {
        ProcessId = processId,
        ClientInfo = new ClientInfo(),
        Capabilities = new ClientCapabilities(),
      }
    });
    await outputHandler.StopAsync();
    return Encoding.ASCII.GetString(buffer.ToArray());
  }

  class AlwaysOutputFilter : IOutputFilter {
    public bool ShouldOutput(object value) => true;
  }
}
