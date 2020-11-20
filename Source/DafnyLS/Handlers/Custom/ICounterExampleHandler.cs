using OmniSharp.Extensions.JsonRpc;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  [Parallel]
  [Method("counterExample", Direction.ClientToServer)]
  public interface ICounterExampleHandler : IJsonRpcRequestHandler<CounterExampleParams, CounterExampleList> {
  }
}
