using MediatR;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  [Method(DafnyRequestNames.CounterExample, Direction.ClientToServer)]
  public class CounterExampleParams : ITextDocumentIdentifierParams, IRequest<CounterExampleList> {
    // TODO Refine nullability. AllowNull is currently ignored in the CI and leads to build warnings.
#pragma warning disable CS8618 // Non-nullable field must contain a non-null value when exiting constructor.
    public TextDocumentIdentifier TextDocument { get; set; }
#pragma warning restore CS8618 // Non-nullable field must contain a non-null value when exiting constructor.
    public int CounterExampleDepth { get; set; } = 5;
  }
}
