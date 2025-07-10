#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using IntervalTree;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny {
  /// <summary>
  /// Text document loader implementation that offloads the whole load procedure on one dedicated
  /// thread with a stack size of 256MB. Since only one thread is used, document loading is implicitely synchronized.
  /// The verification runs on the calling thread.
  /// </summary>
  /// <remarks>
  /// The increased stack size is necessary to solve the issue https://github.com/dafny-lang/dafny/issues/1447.
  /// </remarks>
  public class TextDocumentLoader : ITextDocumentLoader {
    private readonly ILogger<ITextDocumentLoader> logger;
    private readonly IDafnyParser parser;
    private readonly ISymbolResolver symbolResolver;

    public TextDocumentLoader(
      ILogger<ITextDocumentLoader> documentLoader,
      IDafnyParser parser,
      ISymbolResolver symbolResolver) {
      this.logger = documentLoader;
      this.parser = parser;
      this.symbolResolver = symbolResolver;
    }

    public async Task<ProgramParseResult> ParseAsync(Compilation compilation, CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await DafnyMain.LargeStackFactory.StartNew(
        () => parser.Parse(compilation, cancellationToken), cancellationToken
#pragma warning restore CS1998
      );
    }

    public async Task<ResolutionResult?> ResolveAsync(Compilation compilation,
      Program program,
      CancellationToken cancellationToken) {
#pragma warning disable CS1998
      return await await DafnyMain.LargeStackFactory.StartNew(
        () => ResolveInternal(compilation, program, cancellationToken), cancellationToken);
#pragma warning restore CS1998
    }

    private async Task<ResolutionResult?> ResolveInternal(Compilation compilation, Program program, CancellationToken cancellationToken) {
      if (program.HasParseErrors) {
        return null;
      }

      await symbolResolver.ResolveSymbols(compilation, program, cancellationToken);

      if (compilation.ShouldProcessSolverOptions) {
        compilation.Options.ProcessSolverOptions(compilation.Reporter, compilation.Options.DafnyProject.StartingToken);
      }

      IDictionary<Uri, IIntervalTree<DafnyPosition, ICanVerify>>? verifiables;
      if (compilation.HasErrors) {
        verifiables = null;
      } else {
        var symbols = SymbolExtensions.GetSymbolDescendants(program.DefaultModule);
        verifiables = new Dictionary<Uri, IIntervalTree<DafnyPosition, ICanVerify>>();
        foreach (var canVerify in symbols.OfType<ICanVerify>().Where(v =>
                   !v.Origin.IsCopy &&
                   v.ShouldVerify &&
                  v.ContainingModule.ShouldVerify(program.Compilation) &&
                  v.ShouldVerify(program.Compilation)
                  ).ToList()) {
          var forUri =
            verifiables.GetOrCreate(canVerify.Origin.Uri, () => new IntervalTree<DafnyPosition, ICanVerify>());
          var range = canVerify.ReportingRange.ToDafnyRange();
          forUri.Add(
            range.Start,
            range.ExclusiveEnd,
            canVerify);
        }
      }

      return new ResolutionResult(
        compilation.HasErrors,
        program,
        verifiables
      );
    }
  }
}
