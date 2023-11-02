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

public record Resolution(
  Program ResolvedProgram,
  SymbolTable? SymbolTable,
  LegacySignatureAndCompletionTable SignatureAndCompletionTable,
  IReadOnlyDictionary<Uri, IReadOnlyList<Range>> GhostRanges,
  IReadOnlyList<ICanVerify>? CanVerifies);
