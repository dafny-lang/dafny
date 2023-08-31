using System.Collections.Generic;
using System.Collections.Immutable;
using AlcorProofKernel;
using AlcorTacticProofChecker;
using Dafny;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

partial class Translator {
  internal record AlcorAssumptions(Env Environment, ImmutableList<Tactic> Tactics) {
    public AlcorAssumptions WithEnv(Expression assumption, ExpressionTranslator etran, string name = null) {
      return WithEnv(etran.TrExprAlcor(assumption), name);
    }

    public AlcorAssumptions WithEnv(AlcorProofKernel._IExpr alcorExpression, string name = null) {
      var label = 
        Environment.FreshVar(ToDafnyString(name ?? "h"));

      return new AlcorAssumptions(new Env_EnvCons(
        label, alcorExpression, Environment
      ), Tactics);
    }

    public AlcorAssumptions WithAssertedExpr(Expr alcorExpression, [CanBeNull] string labelString) {
      var label = 
        Environment.FreshVar(ToDafnyString(labelString ?? "h"));
      return new AlcorAssumptions(
        new AlcorTacticProofChecker.Env_EnvCons(
          label, alcorExpression, Environment),
        ImmutableList<Tactic>.Empty);
    }
    
    public AlcorAssumptions WithAssumedExpr(Expr alcorExpression, [CanBeNull] string labelString) {
      var label = 
        Environment.FreshVar(ToDafnyString(labelString ?? "h"));
      return new AlcorAssumptions(
        new AlcorTacticProofChecker.Env_EnvCons(
          label, alcorExpression, Environment),
        Tactics);
    }

    public AlcorAssumptions WithTactics(IEnumerable<Tactic> tactics) {
      return new AlcorAssumptions(Environment, Tactics.AddRange(tactics));
    }
  }
}