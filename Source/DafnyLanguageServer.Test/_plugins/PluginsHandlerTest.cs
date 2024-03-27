using OmniSharp.Extensions.LanguageServer.Server;
using MediatR;
using OmniSharp.Extensions.JsonRpc;
using System.Threading;
using System.Threading.Tasks;

namespace PluginsHandlerTest {
  /// <summary>
  ///  Small plugin that adds a request to the language server, which simply returns a dummy string
  /// </summary>
  public class TestConfiguration : Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration {
    public override LanguageServerOptions WithPluginHandlers(LanguageServerOptions options) {
      return options.WithHandler<DummyHandler>();
    }
  }

  [Parallel]
  [Method("dafny/request/dummy", Direction.ClientToServer)]
  public record DummyParams : IRequest<string>;

  public class DummyHandler : IJsonRpcRequestHandler<DummyParams, string> {
    public async Task<string> Handle(DummyParams request, CancellationToken cancellationToken) {
      return "dummy";
    }
  }
}