using System.Collections.Generic;

namespace Microsoft.Dafny; 

public static class Rewriters {
  public static IList<IRewriter> GetRewriters(Program program, FreshIdGenerator idGenerator) {
    var result = new List<IRewriter>();
    var reporter = program.Reporter;

    if (program.Options.AuditProgram) {
      result.Add(new Auditor.Auditor(reporter));
    }

    if (!program.Options.VerifyAllModules) {
      result.Add(new IncludedLemmaBodyRemover(program, reporter));
    }

    result.Add(new AutoContractsRewriter(reporter, program.SystemModuleManager));
    result.Add(new OpaqueMemberRewriter(reporter));
    result.Add(new AutoReqFunctionRewriter(reporter, program.SystemModuleManager));
    result.Add(new TimeLimitRewriter(reporter));
    result.Add(new ForallStmtRewriter(reporter));
    result.Add(new ProvideRevealAllRewriter(reporter));
    result.Add(new MatchFlattener(reporter, idGenerator));

    if (program.Options.AutoTriggers) {
      result.Add(new QuantifierSplittingRewriter(reporter));
      result.Add(new TriggerGeneratingRewriter(reporter));
    }

    if (program.Options.TestContracts != DafnyOptions.ContractTestingMode.None) {
      result.Add(new ExpectContracts(reporter));
    }

    if (program.Options.RunAllTests) {
      result.Add(new RunAllTestsMainMethod(reporter));
    }

    result.Add(new InductionRewriter(reporter));
    result.Add(new PrintEffectEnforcement(reporter));
    result.Add(new BitvectorOptimization(program.SystemModuleManager, reporter));

    if (program.Options.DisallowConstructorCaseWithoutParentheses) {
      result.Add(new ConstructorWarning(reporter));
    }

    result.Add(new LocalLinter(reporter));
    result.Add(new PrecedenceLinter(reporter));
    
    if (program.Options.Get(CommonOptionBag.AllOpaque)) {
      result.Add(new AllOpaqueRevealStmtInserter(reporter));
    }

    foreach (var plugin in program.Options.Plugins) {
      result.AddRange(plugin.GetRewriters(reporter));
    }

    return result;
  }
}