using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<SlowVerifier> logger, IOptions<VerifierOptions> options) {
    verifier = DafnyProgramVerifier.Create(logger, options);
  }

  private readonly DafnyProgramVerifier verifier;

  public IReadOnlyList<IImplementationTask> Verify(Dafny.Program program, IVerificationProgressReporter progressReporter, CancellationToken cancellationToken) {
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();

    var originalResult = verifier.Verify(program, progressReporter, cancellationToken);
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      var source = new TaskCompletionSource<ServerVerificationResult>();
      cancellationToken.Register(() => { source.SetCanceled(cancellationToken); });

      return new List<IImplementationTask>
        { new NeverVerifiesImplementationTask(originalResult[0], cancellationToken) };
    }

    return originalResult;
  }

  class NeverVerifiesImplementationTask : IImplementationTask {
    private readonly IImplementationTask original;
    private readonly TaskCompletionSource<VerificationResult> source;


    public NeverVerifiesImplementationTask(IImplementationTask original, CancellationToken token) {
      this.original = original;
      source = new TaskCompletionSource<VerificationResult>();
      token.Register(() => {
        source.SetCanceled(token);
      });
    }

    public IObservable<VerificationStatus> ObservableStatus => Observable.Empty<VerificationStatus>();
    public VerificationStatus CurrentStatus => VerificationStatus.Verifying;
    public ProcessedProgram ProcessedProgram => original.ProcessedProgram;
    public Implementation Implementation => original.Implementation;
    public Task<VerificationResult> ActualTask => source.Task;

    public void Run() {
      
    }

    public void InitialiseStatus() {
    }
  }
}