using System;
using DafnyServer.CounterexampleGeneration;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;

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
          var translatedDocument = await documentManager.CompilationManager.TranslatedDocument;
          var verificationTasks = translatedDocument.VerificationTasks;
          if (verificationTasks != null) {
            foreach (var task in verificationTasks) {
              documentManager.CompilationManager.Verify(translatedDocument, task);
            }
          }

          var documentWithCounterExamples = await documentManager.LastDocumentAsync;
          return new CounterExampleLoader(logger, documentWithCounterExamples!, request.CounterExampleDepth, cancellationToken)
            .GetCounterExamples();
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
      private const string InitialStateName = "<initial>";
      private static readonly Regex StatePositionRegex = new(
        @".*\.dfy\((?<line>\d+),(?<character>\d+)\)",
        RegexOptions.IgnoreCase | RegexOptions.Singleline
      );

      private readonly ILogger logger;
      private readonly DafnyDocument document;
      private readonly CancellationToken cancellationToken;
      private readonly int counterExampleDepth;

      public CounterExampleLoader(ILogger logger, DafnyDocument document, int counterExampleDepth, CancellationToken cancellationToken) {
        this.logger = logger;
        this.document = document;
        this.cancellationToken = cancellationToken;
        this.counterExampleDepth = counterExampleDepth;
      }

      public CounterExampleList GetCounterExamples() {
        if (!document.Counterexamples!.Any()) {
          logger.LogDebug("got no counter-examples for document {DocumentUri}", document.Uri);
          return new CounterExampleList();
        }
        var counterExamples = GetLanguageSpecificModels(document.Counterexamples!)
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
