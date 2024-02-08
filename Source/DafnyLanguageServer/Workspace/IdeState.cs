using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using VC;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record IdeVerificationTaskState(Range Range, PublishedVerificationStatus Status,
  IReadOnlyList<Diagnostic> Diagnostics, bool HitErrorLimit, IVerificationTask Task, IVerificationStatus RawStatus);

public enum VerificationPreparationState { NotStarted, InProgress, Done }
public record IdeCanVerifyState(VerificationPreparationState PreparationProgress,
  ImmutableDictionary<string, IdeVerificationTaskState> VerificationTasks,
  IReadOnlyList<Diagnostic> Diagnostics);

/// <summary>
/// Contains information from the latest document, and from older documents if some information is missing,
/// to provide the IDE with as much information as possible.
/// </summary>
public record IdeState(
  int Version,
  ISet<Uri> OwnedUris,
  CompilationInput Input,
  CompilationStatus Status,
  Node Program,
  ImmutableDictionary<Uri, ImmutableList<Diagnostic>> StaticDiagnostics,
  Node? ResolvedProgram,
  SymbolTable SymbolTable,
  LegacySignatureAndCompletionTable SignatureAndCompletionTable,
  ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeCanVerifyState>> CanVerifyStates,
  IReadOnlyList<Counterexample> Counterexamples,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  ImmutableDictionary<Uri, DocumentVerificationTree> VerificationTrees
) {
  public Uri Uri => Input.Uri.ToUri();

  public static IEnumerable<Diagnostic> MarkDiagnosticsAsOutdated(IEnumerable<Diagnostic> diagnostics) {
    return diagnostics.Select(diagnostic => diagnostic with {
      Severity = diagnostic.Severity == DiagnosticSeverity.Error ? DiagnosticSeverity.Warning : diagnostic.Severity,
      Message = diagnostic.Message.StartsWith(OutdatedPrefix)
        ? diagnostic.Message
        : OutdatedPrefix + diagnostic.Message
    });
  }

  public static IdeState InitialIdeState(CompilationInput input) {
    var program = new EmptyNode();
    return new IdeState(input.Version, ImmutableHashSet<Uri>.Empty,
      input,
      CompilationStatus.Parsing,
      program,
      ImmutableDictionary<Uri, ImmutableList<Diagnostic>>.Empty,
      program,
      SymbolTable.Empty(),
      LegacySignatureAndCompletionTable.Empty(input.Options, input.Project), ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeCanVerifyState>>.Empty,
      Array.Empty<Counterexample>(),
      ImmutableDictionary<Uri, IReadOnlyList<Range>>.Empty,
      ImmutableDictionary<Uri, DocumentVerificationTree>.Empty
    );
  }

  public const string OutdatedPrefix = "Outdated: ";

  public IdeState Migrate(DafnyOptions options, Migrator migrator, int newVersion, bool clientSide) {
    var migratedVerificationTrees = VerificationTrees.ToImmutableDictionary(
      kv => kv.Key, kv =>
        (DocumentVerificationTree)migrator.RelocateVerificationTree(kv.Value));

    var verificationResults = clientSide
      ? CanVerifyStates
      : MigrateImplementationViews(migrator, CanVerifyStates);
    return this with {
      Version = newVersion,
      Status = CompilationStatus.Parsing,
      CanVerifyStates = verificationResults,
      SignatureAndCompletionTable = options.Get(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable)
        ? migrator.MigrateSymbolTable(SignatureAndCompletionTable) : LegacySignatureAndCompletionTable.Empty(options, Input.Project),
      VerificationTrees = migratedVerificationTrees
    };
  }

  private ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeCanVerifyState>> MigrateImplementationViews(
    Migrator migrator,
    ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeCanVerifyState>> oldVerificationDiagnostics) {
    var uri = migrator.MigratedUri;
    var previous = oldVerificationDiagnostics.GetValueOrDefault(uri);
    if (previous == null) {
      return oldVerificationDiagnostics;
    }
    var result = ImmutableDictionary<Range, IdeCanVerifyState>.Empty;
    foreach (var entry in previous) {
      var newOuterRange = migrator.MigrateRange(entry.Key);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = ImmutableDictionary<string, IdeVerificationTaskState>.Empty;
      foreach (var innerEntry in entry.Value.VerificationTasks) {
        var newInnerRange = migrator.MigrateRange(innerEntry.Value.Range);
        if (newInnerRange != null) {
          newValue = newValue.Add(innerEntry.Key, innerEntry.Value with {
            Range = newInnerRange,
            Diagnostics = migrator.MigrateDiagnostics(innerEntry.Value.Diagnostics)
          });
        }
      }

      result = result.Add(newOuterRange, entry.Value with { VerificationTasks = newValue });
    }

    return oldVerificationDiagnostics.SetItem(uri, result);
  }

  public IReadOnlyDictionary<Range, IdeCanVerifyState> GetVerificationResults(Uri uri) {
    return CanVerifyStates.GetValueOrDefault(uri) ??
      ((IReadOnlyDictionary<Range, IdeCanVerifyState>)ImmutableDictionary<Range, IdeCanVerifyState>.Empty);
  }

  public IEnumerable<Diagnostic> GetAllDiagnostics() {
    return GetDiagnosticUris().SelectMany(GetDiagnosticsForUri);
  }

  public IEnumerable<Diagnostic> GetDiagnosticsForUri(Uri uri) {
    var resolutionDiagnostics = StaticDiagnostics.GetValueOrDefault(uri) ?? Enumerable.Empty<Diagnostic>();
    var verificationDiagnostics = GetVerificationResults(uri).SelectMany(x => {
      var taskDiagnostics = x.Value.VerificationTasks.Values.SelectMany(v => v.Diagnostics);
      return x.Value.Diagnostics.Concat(taskDiagnostics.Concat(GetErrorLimitDiagnostics(x)));
    });
    return resolutionDiagnostics.Concat(verificationDiagnostics);
  }

  private static IEnumerable<Diagnostic> GetErrorLimitDiagnostics(KeyValuePair<Range, IdeCanVerifyState> x) {
    var anyImplementationHitErrorLimit = x.Value.VerificationTasks.Values.Any(i => i.HitErrorLimit);
    IEnumerable<Diagnostic> result;
    if (anyImplementationHitErrorLimit) {
      var diagnostic = new Diagnostic() {
        Severity = DiagnosticSeverity.Warning,
        Code = new DiagnosticCode("errorLimitHit"),
        Message =
          "Verification hit error limit so not all errors may be shown. Configure this limit using --error-limit",
        Range = x.Key,
        Source = MessageSource.Verifier.ToString()
      };
      result = new[] { diagnostic };
    } else {
      result = Enumerable.Empty<Diagnostic>();
    }

    return result;
  }

  public IEnumerable<Uri> GetDiagnosticUris() {
    return StaticDiagnostics.Keys.Concat(CanVerifyStates.Keys);
  }

  public async Task<IdeState> UpdateState(DafnyOptions options,
    ILogger logger,
    TelemetryPublisherBase telemetryPublisher,
    IProjectDatabase projectDatabase, ICompilationEvent e) {
    switch (e) {
      case DeterminedRootFiles determinedRootFiles:
        return await HandleDeterminedRootFiles(options, logger, projectDatabase, determinedRootFiles);
      case BoogieUpdate boogieUpdate:
        return HandleBoogieUpdate(options, logger, boogieUpdate);
      case CanVerifyPartsIdentified canVerifyPartsIdentified:
        return HandleCanVerifyPartsUpdated(logger, canVerifyPartsIdentified);
      case FinishedParsing finishedParsing:
        return HandleFinishedParsing(finishedParsing);
      case FinishedResolution finishedResolution:
        return HandleFinishedResolution(options, logger, telemetryPublisher, finishedResolution);
      case InternalCompilationException internalCompilationException:
        return HandleInternalCompilationException(internalCompilationException);
      case BoogieException boogieException:
        return HandleBoogieException(boogieException);
      case NewDiagnostic newDiagnostic:
        return HandleNewDiagnostic(newDiagnostic);
      case ScheduledVerification scheduledVerification:
        return HandleScheduledVerification(scheduledVerification);
      default:
        throw new ArgumentOutOfRangeException(nameof(e));
    }
  }

  private async Task<IdeState> HandleDeterminedRootFiles(DafnyOptions options, ILogger logger,
    IProjectDatabase projectDatabase, DeterminedRootFiles determinedRootFiles) {

    var errors = determinedRootFiles.Diagnostics.Values.SelectMany(x => x).
      Where(d => d.Severity == DiagnosticSeverity.Error);
    var status = errors.Any() ? CompilationStatus.ParsingFailed : this.Status;

    var ownedUris = new HashSet<Uri>();
    foreach (var file in determinedRootFiles.Roots) {
      var uriProject = await projectDatabase.GetProject(file.Uri);
      var ownedUri = uriProject.Equals(determinedRootFiles.Project);
      if (ownedUri) {
        ownedUris.Add(file.Uri);
      }
    }
    ownedUris.Add(determinedRootFiles.Project.Uri);

    return this with {
      OwnedUris = ownedUris,
      StaticDiagnostics = status == CompilationStatus.ParsingFailed ? determinedRootFiles.Diagnostics : this.StaticDiagnostics,
      Status = status,
      VerificationTrees = determinedRootFiles.Roots.ToImmutableDictionary(
        file => file.Uri,
        file => this.VerificationTrees.GetValueOrDefault(file.Uri) ??
                new DocumentVerificationTree(this.Program, file.Uri))
    };
  }

  private IdeState HandleScheduledVerification(ScheduledVerification scheduledVerification) {
    var previousState = this;

    var uri = scheduledVerification.CanVerify.Tok.Uri;
    var range = scheduledVerification.CanVerify.NameToken.GetLspRange();
    var previousVerificationResult = previousState.CanVerifyStates[uri][range];
    var previousImplementations = previousVerificationResult.VerificationTasks;
    var preparationProgress = new[]
      { previousVerificationResult.PreparationProgress, VerificationPreparationState.InProgress }.Max();
    var verificationResult = new IdeCanVerifyState(PreparationProgress: preparationProgress,
      VerificationTasks: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }), previousVerificationResult.Diagnostics);
    return previousState with {
      CanVerifyStates = previousState.CanVerifyStates.SetItem(uri,
        previousState.CanVerifyStates[uri].SetItem(range, verificationResult))
    };
  }

  private IdeState HandleNewDiagnostic(NewDiagnostic newDiagnostic) {
    var previousState = this;

    // Until resolution is finished, keep showing the old diagnostics. 
    if (previousState.Status > CompilationStatus.ResolutionStarted) {
      var diagnostics = previousState.StaticDiagnostics.GetValueOrDefault(newDiagnostic.Uri, ImmutableList<Diagnostic>.Empty);
      var newDiagnostics = diagnostics.Add(newDiagnostic.Diagnostic.ToLspDiagnostic());
      return previousState with {
        StaticDiagnostics = previousState.StaticDiagnostics.SetItem(newDiagnostic.Uri, newDiagnostics)
      };
    }

    return previousState;
  }

  private IdeState HandleInternalCompilationException(InternalCompilationException internalCompilationException) {
    var previousState = this;
    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        internalCompilationException.Exception,
      Severity = DiagnosticSeverity.Error,
      Range = new Range(0, 0, 0, 1)
    };
    return previousState with {
      Status = CompilationStatus.InternalException,
      StaticDiagnostics =
      ImmutableDictionary<Uri, ImmutableList<Diagnostic>>.Empty.Add(previousState.Input.Uri.ToUri(),
        ImmutableList.Create(internalErrorDiagnostic))
    };
  }

  private IdeState HandleFinishedResolution(DafnyOptions options,
    ILogger logger,
    TelemetryPublisherBase telemetryPublisher,
    FinishedResolution finishedResolution) {
    var previousState = this;
    var errors = finishedResolution.Diagnostics.Values.SelectMany(x => x).Where(d =>
      d.Severity == DiagnosticSeverity.Error && d.Source != MessageSource.Compiler.ToString()).ToList();
    var status = errors.Any() ? CompilationStatus.ResolutionFailed : CompilationStatus.ResolutionSucceeded;

    var cancellationToken = CancellationToken.None; // TODO ?
    SymbolTable? symbolTable = null;
    try {
      symbolTable = SymbolTable.CreateFrom(logger, finishedResolution.Result.ResolvedProgram, cancellationToken);
    } catch (Exception e) {
      logger.LogError(e, "failed to create symbol table");
    }

    var beforeLegacyServerResolution = DateTime.Now;
    var legacySignatureAndCompletionTable = new SymbolTableFactory(logger).CreateFrom(Input,
      finishedResolution.Result, cancellationToken);
    telemetryPublisher.PublishTime("LegacyServerResolution", options.DafnyProject.Uri.ToString(), DateTime.Now - beforeLegacyServerResolution);

    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> ghostRanges = new GhostStateDiagnosticCollector(options, logger).
      GetGhostStateDiagnostics(legacySignatureAndCompletionTable, cancellationToken);

    var trees = previousState.VerificationTrees;
    if (status == CompilationStatus.ResolutionSucceeded) {
      foreach (var uri in trees.Keys) {
        trees = trees.SetItem(uri,
          GutterIconAndHoverVerificationDetailsManager.UpdateTree(options, finishedResolution.Result.ResolvedProgram,
            previousState.VerificationTrees[uri]));
      }
    }

    var verificationResults = finishedResolution.Result.CanVerifies == null
      ? previousState.CanVerifyStates
      : finishedResolution.Result.CanVerifies.GroupBy(l => l.NameToken.Uri).ToImmutableDictionary(k => k.Key,
        k => k.GroupBy<ICanVerify, Range>(l => l.NameToken.GetLspRange()).ToImmutableDictionary(
          l => l.Key,
          l => MergeResults(l.Select(canVerify => MergeVerifiable(previousState, canVerify)))));
    var signatureAndCompletionTable = legacySignatureAndCompletionTable.Resolved
      ? legacySignatureAndCompletionTable
      : previousState.SignatureAndCompletionTable;

    return previousState with {
      StaticDiagnostics = finishedResolution.Diagnostics,
      Status = status,
      Counterexamples = Array.Empty<Counterexample>(),
      ResolvedProgram = finishedResolution.Result.ResolvedProgram,
      SymbolTable = symbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = signatureAndCompletionTable,
      GhostRanges = ghostRanges,
      CanVerifyStates = verificationResults,
      VerificationTrees = trees
    };
  }

  private static IdeCanVerifyState MergeResults(IEnumerable<IdeCanVerifyState> results) {
    return results.Aggregate((a, b) => new IdeCanVerifyState(
      MergeStates(a.PreparationProgress, b.PreparationProgress),
      a.VerificationTasks.ToImmutableDictionary().Merge(b.VerificationTasks,
        (aView, bView) => aView /* Merge should not occur */),
      a.Diagnostics.Concat(b.Diagnostics)));
  }

  private static VerificationPreparationState MergeStates(VerificationPreparationState a, VerificationPreparationState b) {
    return new[] { a, b }.Max();
  }

  private static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }

  private static IdeCanVerifyState MergeVerifiable(IdeState previousState, ICanVerify canVerify) {
    var range = canVerify.NameToken.GetLspRange();
    var previousIdeCanVerifyState = previousState.GetVerificationResults(canVerify.NameToken.Uri).GetValueOrDefault(range);
    var previousImplementations =
      previousIdeCanVerifyState?.VerificationTasks ??
      ImmutableDictionary<string, IdeVerificationTaskState>.Empty;
    return new IdeCanVerifyState(PreparationProgress: VerificationPreparationState.NotStarted,
      VerificationTasks: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }), previousIdeCanVerifyState?.Diagnostics ?? new List<Diagnostic>());
  }

  private IdeState HandleFinishedParsing(FinishedParsing finishedParsing) {
    var previousState = this;
    var trees = previousState.VerificationTrees;
    foreach (var uri in trees.Keys) {
      trees = trees.SetItem(uri,
        new DocumentVerificationTree(finishedParsing.Program, uri) {
          Children = trees[uri].Children
        });
    }

    var errors = finishedParsing.Diagnostics.Values.SelectMany(x => x)
      .Where(d => d.Severity == DiagnosticSeverity.Error);
    var status = errors.Any() ? CompilationStatus.ParsingFailed : CompilationStatus.ResolutionStarted;

    return previousState with {
      Program = finishedParsing.Program,
      StaticDiagnostics = status == CompilationStatus.ParsingFailed
        ? finishedParsing.Diagnostics
        : previousState.StaticDiagnostics,
      Status = status,
      VerificationTrees = trees
    };
  }

  private IdeState HandleCanVerifyPartsUpdated(ILogger logger, CanVerifyPartsIdentified canVerifyPartsIdentified) {
    var previousState = this;
    var implementations = canVerifyPartsIdentified.Parts.Select(t => t.Split.Implementation).Distinct();
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);

    var uri = canVerifyPartsIdentified.CanVerify.Tok.Uri;
    gutterIconManager.ReportImplementationsBeforeVerification(previousState,
      canVerifyPartsIdentified.CanVerify, implementations.ToArray());

    var range = canVerifyPartsIdentified.CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.CanVerifyStates[uri][range].VerificationTasks;
    var names = canVerifyPartsIdentified.Parts.Select(Compilation.GetTaskName);
    var verificationResult = new IdeCanVerifyState(PreparationProgress: VerificationPreparationState.Done,
      VerificationTasks: canVerifyPartsIdentified.Parts.ToImmutableDictionary(Compilation.GetTaskName,
        k => {
          var previous = previousImplementations.GetValueOrDefault(Compilation.GetTaskName(k));
          return new IdeVerificationTaskState(range, PublishedVerificationStatus.Queued,
            previous?.Diagnostics ?? Array.Empty<Diagnostic>(),
            previous?.HitErrorLimit ?? false, k, new Stale());
        }), new List<Diagnostic>());
    return previousState with {
      CanVerifyStates = previousState.CanVerifyStates.SetItem(uri,
        previousState.CanVerifyStates[uri].SetItem(range, verificationResult))
    };
  }

  private IdeState HandleBoogieException(BoogieException boogieException) {
    var previousState = this;

    var name = Compilation.GetTaskName(boogieException.Task);
    var uri = boogieException.CanVerify.Tok.Uri;
    var range = boogieException.CanVerify.NameToken.GetLspRange();

    var previousVerificationResult = previousState.CanVerifyStates[uri][range];
    var previousImplementations = previousVerificationResult.VerificationTasks;
    var previousView = previousImplementations.GetValueOrDefault(name);
    var diagnostics = previousView?.Diagnostics ?? Array.Empty<Diagnostic>();
    var hitErrorLimit = previousView?.HitErrorLimit ?? false;

    var internalErrorDiagnostic = new Diagnostic {
      Message = boogieException.Exception.Message,
      Severity = DiagnosticSeverity.Error,
      Range = range
    };
    diagnostics = diagnostics.Concat(new[] { internalErrorDiagnostic }).ToList();

    var view = new IdeVerificationTaskState(range, PublishedVerificationStatus.Error, diagnostics.ToList(), hitErrorLimit, boogieException.Task, new Stale());

    return previousState with {
      CanVerifyStates = previousState.CanVerifyStates.SetItem(uri,
        previousState.CanVerifyStates[uri].SetItem(range, previousVerificationResult with {
          VerificationTasks = previousVerificationResult.VerificationTasks.SetItem(name, view)
        }))
    };
  }

  private IdeState HandleBoogieUpdate(DafnyOptions options, ILogger logger, BoogieUpdate boogieUpdate) {
    var previousState = this;

    var name = Compilation.GetTaskName(boogieUpdate.VerificationTask);
    var status = StatusFromBoogieStatus(boogieUpdate.BoogieStatus);
    var uri = boogieUpdate.CanVerify.Tok.Uri;
    var range = boogieUpdate.CanVerify.NameToken.GetLspRange();

    var previousVerificationResult = previousState.CanVerifyStates[uri][range];
    var previousImplementations = previousVerificationResult.VerificationTasks;
    var previousView = previousImplementations.GetValueOrDefault(name);
    var counterExamples = previousState.Counterexamples;
    bool hitErrorLimit = previousView?.HitErrorLimit ?? false;
    IVerificationStatus rawStatus = boogieUpdate.BoogieStatus;
    var diagnostics = previousView?.Diagnostics ?? Array.Empty<Diagnostic>();
    if (boogieUpdate.BoogieStatus is Running) {
      diagnostics = Array.Empty<Diagnostic>();
      hitErrorLimit = false;
    }

    if (boogieUpdate.BoogieStatus is Completed completed) {
      // WarnContradictoryAssumptions should be computable after completing a single assertion batch.
      // And we should do this because it allows this warning to be shown when doing --filter-position on a single assertion
      // https://github.com/dafny-lang/dafny/issues/5039 

      counterExamples = counterExamples.Concat(completed.Result.CounterExamples);
      hitErrorLimit |= completed.Result.MaxCounterExamples == completed.Result.CounterExamples.Count;
      var newDiagnostics =
        Compilation.GetDiagnosticsFromResult(options, previousState.Uri, boogieUpdate.VerificationTask, completed.Result);
      diagnostics = newDiagnostics.Select(d => d.ToLspDiagnostic()).ToList();
      logger.LogTrace(
        $"Completed received for {previousState.Input} and found #{diagnostics.Count} diagnostics and #{completed.Result.CounterExamples.Count} counterexamples.");
    }

    var newCanVerifyDiagnostics = new List<Diagnostic>();
    var taskState = new IdeVerificationTaskState(range, status, diagnostics.ToList(),
      hitErrorLimit, boogieUpdate.VerificationTask, rawStatus);
    var newTaskStates = previousVerificationResult.VerificationTasks.SetItem(name, taskState);

    var scopeGroup = newTaskStates.Values.Where(s => s.Task.ScopeId == boogieUpdate.VerificationTask.ScopeId).ToList();
    var allTasksAreCompleted = scopeGroup.All(s => s.Status >= PublishedVerificationStatus.Error);
    if (allTasksAreCompleted) {

      var errorReporter = new ObservableErrorReporter(options, uri);
      List<DafnyDiagnostic> verificationCoverageDiagnostics = new();
      errorReporter.Updates.Subscribe(d => verificationCoverageDiagnostics.Add(d.Diagnostic));

      ProofDependencyWarnings.ReportSuspiciousDependencies(options,
        scopeGroup.Select(s => (s.Task, (Completed)s.RawStatus)),
        errorReporter, boogieUpdate.ProofDependencyManager);

      newCanVerifyDiagnostics = previousVerificationResult.Diagnostics.Concat(verificationCoverageDiagnostics.Select(d => d.ToLspDiagnostic())).ToList();
    }

    UpdateGutterIconTrees(logger, boogieUpdate, scopeGroup);

    return previousState with {
      Counterexamples = counterExamples,
      CanVerifyStates = previousState.CanVerifyStates.SetItem(uri,
        previousState.CanVerifyStates[uri].SetItem(range, previousVerificationResult with {
          VerificationTasks = newTaskStates,
          Diagnostics = newCanVerifyDiagnostics
        }))
    };
  }

  private void UpdateGutterIconTrees(ILogger logger, BoogieUpdate boogieUpdate, IReadOnlyList<IdeVerificationTaskState> scopeGroup) {
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);
    if (boogieUpdate.BoogieStatus is Running && scopeGroup.Count(e => e.Status == PublishedVerificationStatus.Running) == 1) {
      gutterIconManager.ReportVerifyImplementationRunning(this, boogieUpdate.VerificationTask.Split.Implementation);
    }

    if (boogieUpdate.BoogieStatus is Completed completed) {
      gutterIconManager.ReportAssertionBatchResult(this,
        new AssertionBatchResult(boogieUpdate.VerificationTask.Split.Implementation, completed.Result));
    }

    if (scopeGroup.All(e => e.Status >= PublishedVerificationStatus.Error)) {
      var results = scopeGroup.Select(e => e.RawStatus).OfType<Completed>().Select(c => c.Result).ToList();

      foreach (var result in results) {
        logger.LogDebug(
          $"Possibly duplicate reporting assertion batch {result.VcNum}, version {Version}");
        gutterIconManager.ReportAssertionBatchResult(this,
          new AssertionBatchResult(boogieUpdate.VerificationTask.Split.Implementation, result));
      }

      var resourceCount = results.Sum(e => e.ResourceCount);
      var outcome = results.Select(e => Compilation.GetOutcome(e.Outcome)).Max();
      gutterIconManager.ReportEndVerifyImplementation(this, boogieUpdate.VerificationTask.Split.Implementation, resourceCount, outcome);
    }
  }

  private static PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
    switch (verificationStatus) {
      case Stale:
        return PublishedVerificationStatus.Stale;
      case Queued:
        return PublishedVerificationStatus.Queued;
      case Running:
        return PublishedVerificationStatus.Running;
      case Completed completed:
        return completed.Result.Outcome == SolverOutcome.Valid
          ? PublishedVerificationStatus.Correct
          : PublishedVerificationStatus.Error;
      default:
        throw new ArgumentOutOfRangeException();
    }
  }
}