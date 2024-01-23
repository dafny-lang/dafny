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

public record IdeImplementationView(Range Range, PublishedVerificationStatus Status,
  IReadOnlyList<Diagnostic> Diagnostics, bool HitErrorLimit);

public enum VerificationPreparationState { NotStarted, InProgress, Done }
public record IdeVerificationResult(VerificationPreparationState PreparationProgress, ImmutableDictionary<string, IdeImplementationView> Implementations);

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
  ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> VerificationResults,
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
      LegacySignatureAndCompletionTable.Empty(input.Options, input.Project), ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>>.Empty,
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
      ? VerificationResults
      : MigrateImplementationViews(migrator, VerificationResults);
    return this with {
      Version = newVersion,
      Status = CompilationStatus.Parsing,
      VerificationResults = verificationResults,
      SignatureAndCompletionTable = options.Get(LegacySignatureAndCompletionTable.MigrateSignatureAndCompletionTable)
        ? migrator.MigrateSymbolTable(SignatureAndCompletionTable) : LegacySignatureAndCompletionTable.Empty(options, Input.Project),
      VerificationTrees = migratedVerificationTrees
    };
  }

  private ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> MigrateImplementationViews(
    Migrator migrator,
    ImmutableDictionary<Uri, ImmutableDictionary<Range, IdeVerificationResult>> oldVerificationDiagnostics) {
    var uri = migrator.MigratedUri;
    var previous = oldVerificationDiagnostics.GetValueOrDefault(uri);
    if (previous == null) {
      return oldVerificationDiagnostics;
    }
    var result = ImmutableDictionary<Range, IdeVerificationResult>.Empty;
    foreach (var entry in previous) {
      var newOuterRange = migrator.MigrateRange(entry.Key);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = ImmutableDictionary<string, IdeImplementationView>.Empty;
      foreach (var innerEntry in entry.Value.Implementations) {
        var newInnerRange = migrator.MigrateRange(innerEntry.Value.Range);
        if (newInnerRange != null) {
          newValue = newValue.Add(innerEntry.Key, innerEntry.Value with {
            Range = newInnerRange,
            Diagnostics = migrator.MigrateDiagnostics(innerEntry.Value.Diagnostics)
          });
        }
      }

      result = result.Add(newOuterRange, entry.Value with { Implementations = newValue });
    }

    return oldVerificationDiagnostics.SetItem(uri, result);
  }

  public IReadOnlyDictionary<Range, IdeVerificationResult> GetVerificationResults(Uri uri) {
    return VerificationResults.GetValueOrDefault(uri) ??
      ((IReadOnlyDictionary<Range, IdeVerificationResult>)ImmutableDictionary<Range, IdeVerificationResult>.Empty);
  }

  public IEnumerable<Diagnostic> GetAllDiagnostics() {
    return GetDiagnosticUris().SelectMany(GetDiagnosticsForUri);
  }

  public IEnumerable<Diagnostic> GetDiagnosticsForUri(Uri uri) {
    var resolutionDiagnostics = StaticDiagnostics.GetValueOrDefault(uri) ?? Enumerable.Empty<Diagnostic>();
    var verificationDiagnostics = GetVerificationResults(uri).SelectMany(x => {
      return x.Value.Implementations.Values.SelectMany(v => v.Diagnostics).Concat(GetErrorLimitDiagnostics(x));
    });
    return resolutionDiagnostics.Concat(verificationDiagnostics);
  }

  private static IEnumerable<Diagnostic> GetErrorLimitDiagnostics(KeyValuePair<Range, IdeVerificationResult> x) {
    var anyImplementationHitErrorLimit = x.Value.Implementations.Values.Any(i => i.HitErrorLimit);
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
    return StaticDiagnostics.Keys.Concat(VerificationResults.Keys);
  }

  public async Task<IdeState> UpdateState(DafnyOptions options,
    ILogger logger,
    TelemetryPublisherBase telemetryPublisher,
    IProjectDatabase projectDatabase, ICompilationEvent e) {
    switch (e) {
      case DeterminedRootFiles determinedRootFiles:
        return await UpdateDeterminedRootFiles(options, logger, projectDatabase, determinedRootFiles);
      case BoogieUpdate boogieUpdate:
        return UpdateBoogieUpdate(options, logger, boogieUpdate);
      case CanVerifyPartsIdentified canVerifyPartsIdentified:
        return UpdateCanVerifyPartsUpdated(logger, canVerifyPartsIdentified);
      case FinishedParsing finishedParsing:
        return UpdateFinishedParsing(finishedParsing);
      case FinishedResolution finishedResolution:
        return UpdateFinishedResolution(options, logger, telemetryPublisher, finishedResolution);
      case InternalCompilationException internalCompilationException:
        return UpdateInternalCompilationException(internalCompilationException);
      case BoogieException boogieException:
        return UpdateBoogieException(boogieException);
      case NewDiagnostic newDiagnostic:
        return UpdateNewDiagnostic(newDiagnostic);
      case ScheduledVerification scheduledVerification:
        return UpdateScheduledVerification(scheduledVerification);
      default:
        throw new ArgumentOutOfRangeException(nameof(e));
    }
  }

  private async Task<IdeState> UpdateDeterminedRootFiles(DafnyOptions options, ILogger logger,
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

  private IdeState UpdateScheduledVerification(ScheduledVerification scheduledVerification) {
    var previousState = this;

    var uri = scheduledVerification.CanVerify.Tok.Uri;
    var range = scheduledVerification.CanVerify.NameToken.GetLspRange();
    var previousVerificationResult = previousState.VerificationResults[uri][range];
    var previousImplementations = previousVerificationResult.Implementations;
    var preparationProgress = new[]
      { previousVerificationResult.PreparationProgress, VerificationPreparationState.InProgress }.Max();
    var verificationResult = new IdeVerificationResult(PreparationProgress: preparationProgress,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri,
        previousState.VerificationResults[uri].SetItem(range, verificationResult))
    };
  }

  private IdeState UpdateNewDiagnostic(NewDiagnostic newDiagnostic) {
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

  private IdeState UpdateInternalCompilationException(InternalCompilationException internalCompilationException) {
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

  private IdeState UpdateFinishedResolution(DafnyOptions options,
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
      ? previousState.VerificationResults
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
      ResolvedProgram = finishedResolution.Result.ResolvedProgram,
      SymbolTable = symbolTable ?? previousState.SymbolTable,
      SignatureAndCompletionTable = signatureAndCompletionTable,
      GhostRanges = ghostRanges,
      VerificationResults = verificationResults,
      VerificationTrees = trees
    };
  }

  private static IdeVerificationResult MergeResults(IEnumerable<IdeVerificationResult> results) {
    return results.Aggregate((a, b) => new IdeVerificationResult(
      MergeStates(a.PreparationProgress, b.PreparationProgress),
      a.Implementations.ToImmutableDictionary().Merge(b.Implementations,
        (aView, bView) => new IdeImplementationView(
          aView.Range,
          Combine(aView.Status, bView.Status),
          aView.Diagnostics.Concat(bView.Diagnostics).ToList(), aView.HitErrorLimit || bView.HitErrorLimit))));
  }

  private static VerificationPreparationState MergeStates(VerificationPreparationState a, VerificationPreparationState b) {
    return new[] { a, b }.Max();
  }

  private static PublishedVerificationStatus Combine(PublishedVerificationStatus first, PublishedVerificationStatus second) {
    return new[] { first, second }.Min();
  }

  private static IdeVerificationResult MergeVerifiable(IdeState previousState, ICanVerify canVerify) {
    var range = canVerify.NameToken.GetLspRange();
    var previousImplementations =
      previousState.GetVerificationResults(canVerify.NameToken.Uri).GetValueOrDefault(range)?.Implementations ??
      ImmutableDictionary<string, IdeImplementationView>.Empty;
    return new IdeVerificationResult(PreparationProgress: VerificationPreparationState.NotStarted,
      Implementations: previousImplementations.ToImmutableDictionary(kv => kv.Key, kv => kv.Value with {
        Status = PublishedVerificationStatus.Stale,
        Diagnostics = IdeState.MarkDiagnosticsAsOutdated(kv.Value.Diagnostics).ToList()
      }));
  }

  private IdeState UpdateFinishedParsing(FinishedParsing finishedParsing) {
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

  private IdeState UpdateCanVerifyPartsUpdated(ILogger logger, CanVerifyPartsIdentified canVerifyPartsIdentified) {
    var previousState = this;
    var implementations = canVerifyPartsIdentified.Parts.Select(t => t.Implementation);
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);

    var uri = canVerifyPartsIdentified.CanVerify.Tok.Uri;
    gutterIconManager.ReportImplementationsBeforeVerification(previousState,
      canVerifyPartsIdentified.CanVerify, implementations.ToArray());

    var range = canVerifyPartsIdentified.CanVerify.NameToken.GetLspRange();
    var previousImplementations = previousState.VerificationResults[uri][range].Implementations;
    var names = canVerifyPartsIdentified.Parts.Select(t => Compilation.GetImplementationName(t.Implementation));
    var verificationResult = new IdeVerificationResult(PreparationProgress: VerificationPreparationState.Done,
      Implementations: names.ToImmutableDictionary(k => k,
        k => {
          var previous = previousImplementations.GetValueOrDefault(k);
          return new IdeImplementationView(range, PublishedVerificationStatus.Queued,
            previous?.Diagnostics ?? Array.Empty<Diagnostic>(),
            previous?.HitErrorLimit ?? false);
        }));
    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri,
        previousState.VerificationResults[uri].SetItem(range, verificationResult))
    };
  }

  private IdeState UpdateBoogieException(BoogieException boogieException) {
    var previousState = this;

    var name = Compilation.GetImplementationName(boogieException.Task.Implementation);
    var uri = boogieException.CanVerify.Tok.Uri;
    var range = boogieException.CanVerify.NameToken.GetLspRange();

    var previousVerificationResult = previousState.VerificationResults[uri][range];
    var previousImplementations = previousVerificationResult.Implementations;
    var previousView = previousImplementations.GetValueOrDefault(name) ??
                       new IdeImplementationView(range, PublishedVerificationStatus.Error, Array.Empty<Diagnostic>(), false);
    var diagnostics = previousView.Diagnostics;

    var internalErrorDiagnostic = new Diagnostic {
      Message = boogieException.Exception.Message,
      Severity = DiagnosticSeverity.Error,
      Range = range
    };
    diagnostics = diagnostics.Concat(new[] { internalErrorDiagnostic }).ToList();

    var view = new IdeImplementationView(range, PublishedVerificationStatus.Error, diagnostics.ToList(), previousView.HitErrorLimit);

    return previousState with {
      VerificationResults = previousState.VerificationResults.SetItem(uri,
        previousState.VerificationResults[uri].SetItem(range, previousVerificationResult with {
          Implementations = previousVerificationResult.Implementations.SetItem(name, view)
        }))
    };
  }

  private IdeState UpdateBoogieUpdate(DafnyOptions options, ILogger logger, BoogieUpdate boogieUpdate) {
    var previousState = this;
    UpdateGutterIconTrees(boogieUpdate, options, logger);

    var name = Compilation.GetImplementationName(boogieUpdate.ImplementationTask.Implementation);
    var status = StatusFromBoogieStatus(boogieUpdate.BoogieStatus);
    var uri = boogieUpdate.CanVerify.Tok.Uri;
    var range = boogieUpdate.CanVerify.NameToken.GetLspRange();

    var previousVerificationResult = previousState.VerificationResults[uri][range];
    var previousImplementations = previousVerificationResult.Implementations;
    var previousView = previousImplementations.GetValueOrDefault(name) ??
                       new IdeImplementationView(range, status, Array.Empty<Diagnostic>(), false);
    var counterExamples = previousState.Counterexamples;
    bool hitErrorLimit = previousView.HitErrorLimit;
    var diagnostics = previousView.Diagnostics;
    if (boogieUpdate.BoogieStatus is Running) {
      diagnostics = Array.Empty<Diagnostic>();
      counterExamples = Array.Empty<Counterexample>();
      hitErrorLimit = false;
    }

    if (boogieUpdate.BoogieStatus is BatchCompleted batchCompleted) {
      counterExamples = counterExamples.Concat(batchCompleted.VcResult.counterExamples);
      hitErrorLimit |= batchCompleted.VcResult.maxCounterExamples == batchCompleted.VcResult.counterExamples.Count;
      var newDiagnostics =
        Compilation.GetDiagnosticsFromResult(options, previousState.Uri, boogieUpdate.ImplementationTask, batchCompleted.VcResult).ToArray();
      diagnostics = diagnostics.Concat(newDiagnostics.Select(d => d.ToLspDiagnostic())).ToList();
      logger.LogTrace(
        $"BatchCompleted received for {previousState.Input} and found #{newDiagnostics.Length} new diagnostics.");
    }

    if (boogieUpdate.BoogieStatus is Completed completed) {
      var errorReporter = new ObservableErrorReporter(options, uri);
      List<DafnyDiagnostic> verificationCoverageDiagnostics = new();
      errorReporter.Updates.Subscribe(d => verificationCoverageDiagnostics.Add(d.Diagnostic));

      if (Input.Options.Get(CommonOptionBag.WarnContradictoryAssumptions)
          || Input.Options.Get(CommonOptionBag.WarnRedundantAssumptions)) {
        ProofDependencyWarnings.WarnAboutSuspiciousDependenciesForImplementation(Input.Options,
          errorReporter,
          boogieUpdate.ProofDependencyManager,
          new DafnyConsolePrinter.ImplementationLogEntry(boogieUpdate.ImplementationTask.Implementation.VerboseName,
            boogieUpdate.ImplementationTask.Implementation.tok),
          DafnyConsolePrinter.DistillVerificationResult(completed.Result));
      }

      diagnostics = diagnostics.Concat(verificationCoverageDiagnostics.Select(d => d.ToLspDiagnostic())).ToList();
    }

    var view = new IdeImplementationView(range, status, diagnostics.ToList(),
      previousView.HitErrorLimit || hitErrorLimit);
    return previousState with {
      Counterexamples = counterExamples,
      VerificationResults = previousState.VerificationResults.SetItem(uri,
        previousState.VerificationResults[uri].SetItem(range, previousVerificationResult with {
          Implementations = previousVerificationResult.Implementations.SetItem(name, view)
        }))
    };
  }

  private void UpdateGutterIconTrees(BoogieUpdate update, DafnyOptions options, ILogger logger) {
    var gutterIconManager = new GutterIconAndHoverVerificationDetailsManager(logger);
    if (update.BoogieStatus is Running) {
      gutterIconManager.ReportVerifyImplementationRunning(this, update.ImplementationTask.Implementation);
    }

    if (update.BoogieStatus is BatchCompleted batchCompleted) {
      gutterIconManager.ReportAssertionBatchResult(this,
        new AssertionBatchResult(update.ImplementationTask.Implementation, batchCompleted.VcResult));
    }

    if (update.BoogieStatus is Completed completed) {
      var tokenString = BoogieGenerator.ToDafnyToken(true, update.ImplementationTask.Implementation.tok).TokenToString(options);
      var verificationResult = completed.Result;
      // Sometimes, the boogie status is set as Completed
      // but the assertion batches were not reported yet.
      // because they are on a different thread.
      // This loop will ensure that every vc result has been dealt with
      // before we report that the verification of the implementation is finished 
      foreach (var result in completed.Result.VCResults) {
        logger.LogDebug(
          $"Possibly duplicate reporting assertion batch {result.vcNum} as completed in {tokenString}, version {this.Version}");
        gutterIconManager.ReportAssertionBatchResult(this,
          new AssertionBatchResult(update.ImplementationTask.Implementation, result));
      }

      gutterIconManager.ReportEndVerifyImplementation(this, update.ImplementationTask.Implementation, verificationResult);
    }
  }

  private static PublishedVerificationStatus StatusFromBoogieStatus(IVerificationStatus verificationStatus) {
    switch (verificationStatus) {
      case Stale:
        return PublishedVerificationStatus.Stale;
      case Queued:
        return PublishedVerificationStatus.Queued;
      case Running:
      case BatchCompleted:
        return PublishedVerificationStatus.Running;
      case Completed completed:
        return completed.Result.Outcome == ConditionGeneration.Outcome.Correct
          ? PublishedVerificationStatus.Correct
          : PublishedVerificationStatus.Error;
      default:
        throw new ArgumentOutOfRangeException();
    }
  }
}