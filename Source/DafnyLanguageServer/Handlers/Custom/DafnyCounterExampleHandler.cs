using System;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.CounterExampleGeneration;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom {
  public class DafnyCounterExampleHandler : ICounterExampleHandler {
    private readonly DafnyOptions options;
    private readonly ILogger logger;
    private readonly IProjectDatabase projects;
    private readonly TelemetryPublisherBase telemetryPublisher;

    public DafnyCounterExampleHandler(DafnyOptions options,
      ILogger<DafnyCounterExampleHandler> logger,
      IProjectDatabase projects,
      TelemetryPublisherBase telemetryPublisher) {
      this.logger = logger;
      this.projects = projects;
      this.telemetryPublisher = telemetryPublisher;
      this.options = options;
    }

    public async Task<CounterExampleList> Handle(CounterExampleParams request, CancellationToken cancellationToken) {
      try {
        var projectManager = await projects.GetProjectManager(request.TextDocument);
        if (projectManager != null) {
          var uri = request.TextDocument.Uri.ToUri();
          await projectManager.VerifyEverythingAsync(uri);

          var state = await projectManager.States.
            Where(s => FinishedVerifyingUri(s, uri)).FirstAsync();
          logger.LogDebug($"counter-example handler retrieved IDE state, " +
                          $"canVerify count: {state.CanVerifyStates[uri].Count}, " +
                          $"counterExample count: {state.Counterexamples.Count}");
          return new CounterExampleLoader(options, logger, state, request.CounterExampleDepth, cancellationToken).GetCounterExamples();
        }

        logger.LogWarning("counter-examples requested for unloaded document {DocumentUri}",
          request.TextDocument.Uri);
        return new CounterExampleList();
      } catch (OperationCanceledException) {
        logger.LogWarning("counter-examples requested for unverified document {DocumentUri}",
          request.TextDocument.Uri);
        return new CounterExampleList();
      } catch (Exception e) {
        telemetryPublisher.PublishUnhandledException(e);
        return new CounterExampleList();
      }
    }

    private static bool FinishedVerifyingUri(IdeState s, Uri uri) {
      return s.Status == CompilationStatus.ResolutionSucceeded &&
             s.CanVerifyStates[uri].Values.All(r =>
               r.PreparationProgress == VerificationPreparationState.Done &&
               r.VerificationTasks.Values.All(v => v.Status >= PublishedVerificationStatus.Error));
    }

    private class CounterExampleLoader {
      private readonly DafnyOptions options;
      private readonly ILogger logger;
      private readonly IdeState ideState;
      private readonly CancellationToken cancellationToken;
      private readonly int counterExampleDepth;

      public CounterExampleLoader(DafnyOptions options, ILogger logger, IdeState ideState, int counterExampleDepth, CancellationToken cancellationToken) {
        this.options = options;
        this.logger = logger;
        this.ideState = ideState;
        this.cancellationToken = cancellationToken;
        this.counterExampleDepth = counterExampleDepth;
      }

      public CounterExampleList GetCounterExamples() {
        if (!ideState.Counterexamples.Any()) {
          logger.LogDebug($"got no counter-examples for version {ideState.Version}");
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
        return new(model, options);
      }

      private IEnumerable<CounterExampleItem> GetCounterExamples(DafnyModel model) {
        return model.States
          .Where(state => !state.IsInitialState)
          .Select(GetCounterExample);
      }

      private CounterExampleItem GetCounterExample(DafnyModelState state) {
        List<DafnyModelVariable> vars = state.ExpandedVariableSet(counterExampleDepth);
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
