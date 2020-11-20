using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class DafnyCounterExampleHandler : ICounterExampleHandler {
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;

    public DafnyCounterExampleHandler(ILogger<DafnyCounterExampleHandler> logger, IDocumentDatabase documents) {
      _logger = logger;
      _documents = documents;
    }

    public Task<CounterExampleList> Handle(CounterExampleParams request, CancellationToken cancellationToken) {
      return Task.FromResult(new CounterExampleList());
    }
  }
}
