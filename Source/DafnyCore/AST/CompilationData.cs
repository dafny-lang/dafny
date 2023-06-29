using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public class CompilationData {
  public readonly FreshIdGenerator IdGenerator = new();

  public CompilationData(ErrorReporter errorReporter, List<Include> includes, IList<Uri> rootSourceUris, ISet<Uri> alreadyVerifiedRoots, ISet<Uri> alreadyCompiledRoots) {
    Includes = includes;
    ErrorReporter = errorReporter;
    RootSourceUris = rootSourceUris;
    AlreadyVerifiedRoots = alreadyVerifiedRoots;
    AlreadyCompiledRoots = alreadyCompiledRoots;

    Rewriters = GetRewriters();
  }

  public IList<IRewriter> Rewriters { get; private set; }

  public DafnyOptions Options => ErrorReporter.Options;
  public ErrorReporter ErrorReporter { get; }
  public IList<Uri> RootSourceUris { get; }

  public ISet<Uri> AlreadyVerifiedRoots { get; }
  public ISet<Uri> AlreadyCompiledRoots { get; }

  public List<Include> Includes;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToVerify;
  // TODO move to DocumentAfterParsing once that's used by the CLI
  [FilledInDuringResolution]
  public ISet<Uri> UrisToCompile;


  private IList<IRewriter> GetRewriters() {
    var result = new List<IRewriter>();
    var reporter = ErrorReporter;

    result.Add(new RefinementTransformer(reporter));
    if (Options.AuditProgram) {
      result.Add(new Auditor.Auditor(reporter));
    }

    result.Add(new AutoContractsRewriter(reporter));
    result.Add(new OpaqueMemberRewriter(reporter));
    result.Add(new AutoReqFunctionRewriter(reporter));
    result.Add(new TimeLimitRewriter(reporter));
    result.Add(new ForallStmtRewriter(reporter));
    result.Add(new ProvideRevealAllRewriter(reporter));
    result.Add(new MatchFlattener(reporter, IdGenerator));

    if (Options.AutoTriggers) {
      result.Add(new QuantifierSplittingRewriter(reporter));
      result.Add(new TriggerGeneratingRewriter(reporter));
    }

    if (Options.TestContracts != DafnyOptions.ContractTestingMode.None) {
      result.Add(new ExpectContracts(reporter));
    }

    if (Options.RunAllTests) {
      result.Add(new RunAllTestsMainMethod(reporter));
    }

    result.Add(new InductionRewriter(reporter));
    result.Add(new PrintEffectEnforcement(reporter));
    result.Add(new BitvectorOptimization(reporter));

    if (Options.DisallowConstructorCaseWithoutParentheses) {
      result.Add(new ConstructorWarning(reporter));
    }

    result.Add(new LocalLinter(reporter));
    result.Add(new PrecedenceLinter(reporter, this));

    foreach (var plugin in Options.Plugins) {
      result.AddRange(plugin.GetRewriters(reporter));
    }

    return result;
  }
}