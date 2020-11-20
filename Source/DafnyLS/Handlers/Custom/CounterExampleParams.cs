using MediatR;
using System.Diagnostics.CodeAnalysis;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class CounterExampleParams : IRequest<CounterExampleList> {
    // TODO Use LSP's DocumentUri.
    [AllowNull]
    public string DafnyFile { get; set; }
  }
}
