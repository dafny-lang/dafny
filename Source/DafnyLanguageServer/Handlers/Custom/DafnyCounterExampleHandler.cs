using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class DafnyCounterExampleHandler : ICounterExampleHandler {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyCounterExampleHandler(ILogger<DafnyCounterExampleHandler> logger, IDocumentDatabase documents) {
      this.logger = logger;
      this.documents = documents;
    }

    public async Task<CounterExampleList> Handle(CounterExampleParams request, CancellationToken cancellationToken) {
      try {
        var documentManager = documents.GetDocumentManager(request.TextDocument);
        if (documentManager != null) {
          var translatedDocument = await documentManager.Compilation.TranslatedDocument;
          var verificationTasks = translatedDocument.VerificationTasks;
          foreach (var task in verificationTasks) {
            documentManager.Compilation.VerifyTask(translatedDocument, task);
          }

          var state = await documentManager.GetIdeStateAfterVerificationAsync();
          logger.LogDebug("counter-examples retrieved IDE state");
          return new CounterExampleLoader(logger, state, request.CounterExampleDepth, cancellationToken).GetCounterExamples();
        }

        logger.LogWarning("counter-examples requested for unloaded document {DocumentUri}",
          request.TextDocument.Uri);
        return new CounterExampleList();
      } catch (TaskCanceledException) {
        logger.LogWarning("counter-examples requested for unverified document {DocumentUri}",
          request.TextDocument.Uri);
        return new CounterExampleList();
      }
    }

    private class CounterExampleLoader {
      private readonly ILogger logger;
      private readonly IdeState ideState;
      private readonly CancellationToken cancellationToken;
      private readonly int counterExampleDepth;

      public CounterExampleLoader(ILogger logger, IdeState ideState, int counterExampleDepth, CancellationToken cancellationToken) {
        this.logger = logger;
        this.ideState = ideState;
        this.cancellationToken = cancellationToken;
        this.counterExampleDepth = counterExampleDepth;
      }

      public CounterExampleList GetCounterExamples() {
        if (!ideState.Counterexamples.Any()) {
          logger.LogDebug("got no counter-examples for document {DocumentUri}", ideState.Uri);
          return new CounterExampleList();
        }
        var counterExamples = GetLanguageSpecificModels(ideState.Counterexamples)
          .SelectMany(GetCounterExamples)
          .WithCancellation(cancellationToken)
          .ToArray();
        return new CounterExampleList(counterExamples);
      }

      private IEnumerable<DafnyModel> GetLanguageSpecificModels(IReadOnlyList<Counterexample> counterExamples) {
        return counterExamples.Select(c => GetLanguageSpecificModel(c.Model));
      }

      private DafnyModel GetLanguageSpecificModel(Model model) {
        return new(model);
      }

      private IEnumerable<CounterExampleItem> GetCounterExamples(DafnyModel model) {
        return model.States
          .Where(state => !state.IsInitialState)
          .Select(GetCounterExample);
      }

      private CounterExampleItem GetCounterExample(DafnyModelState state) {
        HashSet<DafnyModelVariable> vars = state.ExpandedVariableSet(counterExampleDepth);
        return new(
          new Position(state.GetLineId() - 1, state.GetCharId()),
          vars.WithCancellation(cancellationToken).ToDictionary(
            variable => variable.ShortName + ":" + DafnyModelTypeUtils.GetInDafnyFormat(variable.Type),
            variable => variable.Value
          )
        );
      }
    }
  }
}
