using System;
using System.Collections.Immutable;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public record FinishedParsing(ProgramParseResult ParseResult) : ICompilationEvent;