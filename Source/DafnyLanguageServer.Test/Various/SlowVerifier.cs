using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<IProgramVerifier> logger, IOptions<VerifierOptions> options) {
    verifier = DafnyProgramVerifier.Create(logger, options);
  }

  private readonly DafnyProgramVerifier verifier;

  public IReadOnlyList<IImplementationTask> Verify(Dafny.Program program, IVerificationProgressReporter progressReporter, CancellationToken cancellationToken) {
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      var source = new TaskCompletionSource<ServerVerificationResult>();
      cancellationToken.Register(() => {
        source.SetCanceled(cancellationToken);
      });
      return new List<IImplementationTask> { new MyTask(cancellationToken) };
    }
  
    return verifier.Verify(program, progressReporter, cancellationToken);
  }

  class MyTask : IImplementationTask {
    private readonly TaskCompletionSource<VerificationResult> source;

    public MyTask(CancellationToken token) {

      source = new TaskCompletionSource<VerificationResult>();
      token.Register(() => {
        source.SetCanceled(token);
      });
    }

    public Task<VerificationResult> ActualTask => source.Task;

    public void Run() {
    }
  }
}