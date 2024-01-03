using System;
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public record ResolutionResult(
  Program ResolvedProgram,
  SymbolTable? SymbolTable,
  LegacySignatureAndCompletionTable SignatureAndCompletionTable,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  IReadOnlyList<ICanVerify>? CanVerifies);
