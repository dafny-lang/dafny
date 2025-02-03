using System;
using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.CommandLine;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using AstElement = System.Object;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  public class LegacySignatureAndCompletionTable {

    public static readonly Option<bool> MigrateSignatureAndCompletionTable = new("--migrate-signature-and-completion-table", () => true) {
      IsHidden = true
    };

    private readonly ILogger logger;

    // TODO Guard the properties from changes
    public CompilationUnit CompilationUnit { get; }

    /// <summary>
    /// Gets the dictionary providing a mapping from an Ast Element to the symbol backing it.
    /// </summary>
    public IDictionary<AstElement, ILocalizableSymbol> Declarations { get; }

    /// <summary>
    /// Gets the dictionary allowing to resolve the location of a specified symbol. Do not modify this instance.
    /// </summary>
    public ImmutableDictionary<Uri, IDictionary<ILegacySymbol, SymbolLocation>> LocationsPerUri { get; }

    /// <summary>
    /// Gets the interval tree backing this symbol table. Do not modify this instance.
    /// </summary>
    public ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>> LookupTreePerUri { get; }

    /// <summary>
    /// <c>true</c> if the symbol table results from a successful resolution by the dafny resolver.
    /// </summary>
    public bool Resolved { get; }

    private readonly DafnyLangTypeResolver typeResolver;

    public static LegacySignatureAndCompletionTable Empty(DafnyOptions options, DafnyProject project) {
      var emptyProgram = GetEmptyProgram(options, project.Uri);
      return new LegacySignatureAndCompletionTable(
        NullLogger<LegacySignatureAndCompletionTable>.Instance,
        new CompilationUnit(project.Uri, emptyProgram),
        new Dictionary<object, ILocalizableSymbol>(),
        ImmutableDictionary<Uri, IDictionary<ILegacySymbol, SymbolLocation>>.Empty,
        ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>>.Empty,
        symbolsResolved: false);
    }

    private static readonly ConditionalWeakTable<DafnyOptions, SystemModuleManager> systemModuleManagers = new();

    public static Program GetEmptyProgram(DafnyOptions options, Uri uri) {
      var outerModule = new DefaultModuleDefinition();
      var errorReporter = new ObservableErrorReporter(options, uri);
      var compilation = new CompilationData(errorReporter, [], new List<Uri>(), Sets.Empty<Uri>(),
        Sets.Empty<Uri>());

      SystemModuleManager manager;
      lock (options) {
        if (!systemModuleManagers.TryGetValue(options, out manager!)) {
          manager = new SystemModuleManager(options);
          systemModuleManagers.Add(options, manager);
        }
      }

      var emptyProgram = new Program(
                           uri.ToString(),
        new LiteralModuleDecl(options, outerModule, null, Guid.NewGuid()),
        // BuiltIns cannot be initialized without Type.ResetScopes() before.
        manager,
        errorReporter, compilation
      );
      return emptyProgram;
    }

    public LegacySignatureAndCompletionTable(
        ILogger iLogger,
        CompilationUnit compilationUnit,
        IDictionary<AstElement, ILocalizableSymbol> declarations,
        ImmutableDictionary<Uri, IDictionary<ILegacySymbol, SymbolLocation>> locationsPerUri,
        ImmutableDictionary<Uri, IIntervalTree<Position, ILocalizableSymbol>> lookupTreePerUri,
        bool symbolsResolved
    ) {
      CompilationUnit = compilationUnit;
      Declarations = declarations;
      LocationsPerUri = locationsPerUri;
      LookupTreePerUri = lookupTreePerUri;
      Resolved = symbolsResolved;
      typeResolver = new DafnyLangTypeResolver(declarations);
      logger = iLogger;
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// Only used for testing.
    /// </summary>
    public bool TryGetSymbolAt(Position position, [NotNullWhen(true)] out ILocalizableSymbol? symbol) {
      var intervalTree = LookupTreePerUri.First().Value;

      var symbolsAtPosition = intervalTree.Query(position);
      symbol = null;
      // Use case: function f(a: int) {}, and hover over a.
      foreach (var potentialSymbol in symbolsAtPosition) {
        if (symbol != null) {
          logger.Log(LogLevel.Warning, "Two registered symbols as the same position (line {Line}, character {Character})", position.Line, position.Character);
          break;
        }

        symbol = potentialSymbol;
      }
      return symbol != null;
    }

    /// <summary>
    /// Resolves the innermost symbol that encloses the given position.
    /// </summary>
    /// <param name="uri"></param>
    /// <param name="position">The position to get the innermost symbol of.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The innermost symbol at the specified position.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public ILegacySymbol GetEnclosingSymbol(Uri uri, Position position, CancellationToken cancellationToken) {
      // TODO use a suitable data-structure to resolve the locations efficiently.
      ILegacySymbol innerMostSymbol = CompilationUnit;
      var innerMostRange = new Range(new Position(0, 0), new Position(int.MaxValue, int.MaxValue));
      foreach (var (symbol, location) in LocationsPerUri.GetValueOrDefault(uri) ?? ImmutableDictionary<ILegacySymbol, SymbolLocation>.Empty) {
        cancellationToken.ThrowIfCancellationRequested();
        var range = location.Declaration;
        if (IsEnclosedBy(innerMostRange, range) && IsInside(range, position)) {
          innerMostSymbol = symbol;
          innerMostRange = range;
        }
      }
      return innerMostSymbol;
    }

    private static bool IsEnclosedBy(Range current, Range tested) {
      return tested.Start.CompareTo(current.Start) >= 0
        && tested.End.CompareTo(current.End) <= 0;
    }

    private static bool IsInside(Range range, Position position) {
      return position.CompareTo(range.Start) >= 0
        && position.CompareTo(range.End) <= 0;
    }

    /// <summary>
    /// Tries to resolve the type of the given symbol.
    /// </summary>
    /// <param name="symbol">The symbol to get the type of.</param>
    /// <param name="type">The type of the symbol, or <c>null</c> if the type could not be resolved. If <paramref name="symbol"/> is already a type, it is returned.</param>
    /// <returns><c>true</c> if the type was successfully resolved, otherwise <c>false</c>.</returns>
    public bool TryGetTypeOf(ILegacySymbol symbol, [NotNullWhen(true)] out ILegacySymbol? type) {
      if (symbol is TypeWithMembersSymbolBase) {
        // TODO other type symbols should be supported in the future.
        type = symbol;
        return true;
      }
      var dafnyType = symbol switch {
        FieldSymbol field => field.Declaration.Type,
        VariableSymbol variable => variable.Declaration.Type,
        _ => null
      };
      if (dafnyType == null) {
        type = null;
        return false;
      }
      return typeResolver.TryGetTypeSymbol(dafnyType, out type);
    }
  }
}
