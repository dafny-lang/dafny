using System.Collections.Generic;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public static class RewriterCollection {

  public static IList<IRewriter> GetRewriters(ErrorReporter reporter, Program program) {
    var result = new List<IRewriter>();

    result.Add(new RefinementTransformer(reporter));
    if (reporter.Options.AuditProgram) {
      result.Add(new Auditor.Auditor(reporter));
    }
    result.Add(new ExpandAtAttributes(program, reporter));
    result.Add(new AutoContractsRewriter(program, reporter));
    result.Add(new OpaqueMemberRewriter(reporter));
    result.Add(new AutoReqFunctionRewriter(program, reporter));
    result.Add(new TimeLimitRewriter(reporter));
    result.Add(new ForallStmtRewriter(reporter));
    result.Add(new ProvideRevealAllRewriter(reporter));
    result.Add(new MatchFlattener(reporter));

    if (reporter.Options.AutoTriggers) {
      result.Add(new QuantifierSplittingRewriter(reporter));
      result.Add(new TriggerGeneratingRewriter(reporter, program.SystemModuleManager));
    }

    if (reporter.Options.TestContracts != DafnyOptions.ContractTestingMode.None) {
      result.Add(new ExpectContracts(reporter, program.SystemModuleManager));
    }

    if (reporter.Options.Get(RunAllTestsMainMethod.IncludeTestRunner)) {
      result.Add(new RunAllTestsMainMethod(reporter));
    }

    result.Add(new InductionRewriter(reporter));
    result.Add(new PrintEffectEnforcement(reporter));
    result.Add(new BitvectorOptimization(program, reporter));

    if (reporter.Options.DisallowConstructorCaseWithoutParentheses) {
      result.Add(new ConstructorWarning(reporter));
    }

    result.Add(new LocalLinter(reporter));
    if (!reporter.Options.Get(CommonOptionBag.IgnoreIndentation)) {
      result.Add(new PrecedenceLinter(reporter, program.Compilation));
    }

    if (reporter.Options.Get(CommonOptionBag.DefaultFunctionOpacity) == CommonOptionBag.DefaultFunctionOpacityOptions.AutoRevealDependencies) {
      result.Add(new AutoRevealFunctionDependencies(reporter));
    }

    foreach (var plugin in reporter.Options.Plugins) {
      result.AddRange(plugin.GetRewriters(reporter));
    }

    return result;
  }
}