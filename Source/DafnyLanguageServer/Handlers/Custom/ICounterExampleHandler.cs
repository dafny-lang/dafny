using OmniSharp.Extensions.JsonRpc;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  [Parallel]
  [Method(DafnyRequestNames.CounterExample, Direction.ClientToServer)]
  public interface ICounterExampleHandler : IJsonRpcRequestHandler<CounterExampleParams, CounterExampleList> {
  }
}
