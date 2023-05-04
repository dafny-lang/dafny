using System;
using IntervalTree;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Threading;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using AstElement = System.Object;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  /// <summary>
  /// Represents the symbol table
  /// </summary>
  public class SignatureAndCompletionTable {
    private readonly ILogger<SignatureAndCompletionTable> logger;

    // TODO Guard the properties from changes
    public CompilationUnit CompilationUnit { get; }

    /// <summary>
    /// Gets the dictionary providing a mapping from an Ast Element to the symbol backing it.
    /// </summary>
    public IDictionary<AstElement, ILocalizableSymbol> Declarations { get; }

    /// <summary>
    /// Gets the dictionary allowing to resolve the location of a specified symbol. Do not modify this instance.
    /// </summary>
    public IDictionary<ISymbol, SymbolLocation> Locations { get; }

    /// <summary>
    /// Gets the interval tree backing this symbol table. Do not modify this instance.
    /// </summary>
    public IIntervalTree<Position, ILocalizableSymbol> LookupTree { get; }

    /// <summary>
    /// <c>true</c> if the symbol table results from a successful resolution by the dafny resolver.
    /// </summary>
    public bool Resolved { get; }

    private readonly DafnyLangTypeResolver typeResolver;

    public static SignatureAndCompletionTable Empty(DafnyOptions options, DocumentTextBuffer textDocument) {
      var errorReporter = new DiagnosticErrorReporter(options, textDocument.Text, textDocument.Uri);
      return new SignatureAndCompletionTable(
        NullLogger<SignatureAndCompletionTable>.Instance,
        new CompilationUnit(textDocument.Uri.ToUri(), new Dafny.Program(
          textDocument.Uri.ToString(),
          new List<Uri>() { textDocument.Uri.ToUri()},
          new LiteralModuleDecl(new DefaultModuleDefinition(), null),
          // BuiltIns cannot be initialized without Type.ResetScopes() before.
          new BuiltIns(options), // TODO creating a BuiltIns is a heavy operation
          errorReporter
        )),
        new Dictionary<object, ILocalizableSymbol>(),
        new Dictionary<ISymbol, SymbolLocation>(),
        new IntervalTree<Position, ILocalizableSymbol>(),
        symbolsResolved: false);
    }

    public SignatureAndCompletionTable(
        ILogger<SignatureAndCompletionTable> iLogger,
        CompilationUnit compilationUnit,
        IDictionary<AstElement, ILocalizableSymbol> declarations,
        IDictionary<ISymbol, SymbolLocation> locations,
        IIntervalTree<Position, ILocalizableSymbol> lookupTree,
        bool symbolsResolved
    ) {
      CompilationUnit = compilationUnit;
      Declarations = declarations;
      Locations = locations;
      LookupTree = lookupTree;
      Resolved = symbolsResolved;
      typeResolver = new DafnyLangTypeResolver(declarations);
      logger = iLogger;

      // TODO IntervalTree goes out of sync after any change and "fixes" its state upon the first query. Replace it with another implementation that can be queried without potential side-effects.
      LookupTree.Query(new Position(0, 0));
    }

    /// <summary>
    /// Tries to get a symbol at the specified location.
    /// </summary>
    /// <param name="position">The requested position.</param>
    /// <param name="symbol">The symbol that could be identified at the given position, or <c>null</c> if no symbol could be identified.</param>
    /// <returns><c>true</c> if a symbol was found, otherwise <c>false</c>.</returns>
    /// <exception cref="System.InvalidOperationException">Thrown if there was one more symbol at the specified position. This should never happen, unless there was an error.</exception>
    public bool TryGetSymbolAt(Position position, [NotNullWhen(true)] out ILocalizableSymbol? symbol) {
      var symbolsAtPosition = LookupTree.Query(position);
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
    /// Tries to get the location of the given symbol.
    /// </summary>
    /// <param name="symbol">The symbol to get the location of.</param>
    /// <param name="location">The current location of the specified symbol, or <c>null</c> if no location of the given symbol is known.</param>
    /// <returns><c>true</c> if a location was found, otherwise <c>false</c>.</returns>
    public bool TryGetLocationOf(ISymbol symbol, [NotNullWhen(true)] out SymbolLocation? location) {
      return Locations.TryGetValue(symbol, out location);
    }

    /// <summary>
    /// Resolves the innermost symbol that encloses the given position.
    /// </summary>
    /// <param name="position">The position to get the innermost symbol of.</param>
    /// <param name="cancellationToken">A token to cancel the update operation before its completion.</param>
    /// <returns>The innermost symbol at the specified position.</returns>
    /// <exception cref="System.OperationCanceledException">Thrown when the cancellation was requested before completion.</exception>
    /// <exception cref="System.ObjectDisposedException">Thrown if the cancellation token was disposed before the completion.</exception>
    public ISymbol GetEnclosingSymbol(Position position, CancellationToken cancellationToken) {
      // TODO use a suitable data-structure to resolve the locations efficiently.
      ISymbol innerMostSymbol = CompilationUnit;
      var innerMostRange = new Range(new Position(0, 0), new Position(int.MaxValue, int.MaxValue));
      foreach (var (symbol, location) in Locations) {
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
    public bool TryGetTypeOf(ISymbol symbol, [NotNullWhen(true)] out ISymbol? type) {
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
