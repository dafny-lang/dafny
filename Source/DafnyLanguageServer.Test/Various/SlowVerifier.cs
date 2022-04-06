using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

/// If any top-level declaration has an attribute `{:neverVerify}`,
/// this verifier will return a task that only completes when cancelled
/// which can be useful to test against race conditions
class SlowVerifier : IProgramVerifier {
  public SlowVerifier(ILogger<DafnyProgramVerifier> logger, IOptions<VerifierOptions> options) {
    verifier = DafnyProgramVerifier.Create(logger, options);
  }

  private readonly DafnyProgramVerifier verifier;

  public Task<VerificationResult> VerifyAsync(Dafny.Program program, IVerificationProgressReporter progressReporter, CancellationToken cancellationToken) {
    var attributes = program.Modules().SelectMany(m => {
      return m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().SelectMany(d => d.Members.Select(member => member.Attributes));
    }).ToList();
    if (attributes.Any(a => Attributes.Contains(a, "neverVerify"))) {
      var source = new TaskCompletionSource<VerificationResult>();
      cancellationToken.Register(() => {
        source.SetCanceled(cancellationToken);
      });
      return source.Task;
    }

    return verifier.VerifyAsync(program, progressReporter, cancellationToken);
  }
}