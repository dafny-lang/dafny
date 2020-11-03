using Microsoft.Dafny.LanguageServer;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.JsonRpc.Testing;
using OmniSharp.Extensions.LanguageProtocol.Testing;
using OmniSharp.Extensions.LanguageServer.Server;
using System.IO;
using System.IO.Pipelines;

namespace DafnyLS.IntegrationTest {
  public class IntegrationTestBase : LanguageServerTestBase {
    public IntegrationTestBase() : base(new JsonRpcTestOptions(LoggerFactory.Create(builder => builder.AddConsole().SetMinimumLevel(LogLevel.Warning)))) { }

    protected override (Stream clientOutput, Stream serverInput) SetupServer() {
      var clientPipe = new Pipe(TestOptions.DefaultPipeOptions);
      var serverPipe = new Pipe(TestOptions.DefaultPipeOptions);
      var server = LanguageServer.PreInit(
        options => options
          .WithInput(serverPipe.Reader)
          .WithOutput(clientPipe.Writer)
          .ConfigureLogging(builder => builder.AddConsole().SetMinimumLevel(LogLevel.Debug))
          .WithDafnyLanguageServer()
      );
      server.Initialize(CancellationToken);
      return (clientPipe.Reader.AsStream(), serverPipe.Writer.AsStream());
    }
  }
}
