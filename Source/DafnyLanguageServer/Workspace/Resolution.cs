using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public class Resolution {

  public Resolution(
    Program ResolvedProgram,
    SymbolTable? symbolTable,
    LegacySignatureAndCompletionTable signatureAndCompletionTable,
    IReadOnlyDictionary<Uri, IReadOnlyList<Range>> ghostDiagnostics,
    IReadOnlyList<ICanVerify>? canVerifies,
    LazyConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> translatedModules
    ) {
    this.ResolvedProgram = ResolvedProgram;
    SymbolTable = symbolTable;
    SignatureAndCompletionTable = signatureAndCompletionTable;
    GhostDiagnostics = ghostDiagnostics;
    CanVerifies = canVerifies;
    TranslatedModules = translatedModules;
  }

  public Program ResolvedProgram { get; }
  public SymbolTable? SymbolTable { get; }
  public LegacySignatureAndCompletionTable SignatureAndCompletionTable { get; }
  public IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostDiagnostics { get; }
  public IReadOnlyList<ICanVerify>? CanVerifies { get; }

  // TODO Move?
  public ConcurrentDictionary<ICanVerify, Unit> VerifyingOrVerifiedSymbols { get; } = new();
  public LazyConcurrentDictionary<ICanVerify, Dictionary<string, ImplementationState>> ImplementationsPerVerifiable { get; } = new();

  /// <summary>
  /// FilePosition is required because the default module lives in multiple files
  /// </summary>
  public LazyConcurrentDictionary<ModuleDefinition, Task<IReadOnlyDictionary<FilePosition, IReadOnlyList<IImplementationTask>>>> TranslatedModules { get; }

}
