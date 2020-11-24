using MediatR;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Diagnostics.CodeAnalysis;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  [Method(DafnyRequestNames.CounterExample, Direction.ClientToServer)]
  public class CounterExampleParams : IRequest<CounterExampleList> {
    [AllowNull]
    public TextDocumentIdentifier TextDocument { get; set; }
  }
}
