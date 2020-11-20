using MediatR;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleParams : IRequest<CounterExampleList> {
  }
}
