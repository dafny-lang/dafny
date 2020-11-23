using MediatR;
using OmniSharp.Extensions.JsonRpc;
using System.Diagnostics.CodeAnalysis;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  [Method(DafnyRequestNames.CounterExample, Direction.ClientToServer)]
  public class CounterExampleParams : IRequest<CounterExampleList> {
    // TODO Use LSP's DocumentUri.
    [AllowNull]
    public string DafnyFile { get; set; }
  }
}
