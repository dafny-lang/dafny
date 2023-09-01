using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
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

    public bool Prove(_IExpr alcorExpression, ErrorReporter reporter, out string msg) {
      var provenByAlcor = false;
      msg = "";
      if (Tactics.Any()) {
        // We execute the tactics that were provided by the user
        var tacticMode = new TacticMode();
        tacticMode.__ctor(alcorExpression, Environment);
        var currentState = FromDafnyString(tacticMode.proofState._ToString());
        foreach (var tactic in Tactics) {
          reporter.Info(MessageSource.Verifier, tactic.Token, currentState);
          if (tactic is Intro {Name: var name}) {
            tacticMode.Intro(ToDafnyString(name ?? ""));
          } else if (tactic is ImpElim {NameHyp: var nameHyp, NameImp: var nameImp, NameResult:var nameResult}) {
            tacticMode.ImpElim(ToDafnyString(nameImp ?? ""), ToDafnyString(nameHyp ?? ""),
              ToDafnyString(nameResult ?? ""));
          } else if (tactic is Cases {
                       NameEnvVar: var envVar, NewNameLeft: var newNameLeft, NewNameRight: var newNameRight
                     }) {
            if (envVar == null || newNameLeft == null || newNameRight == null) {
              tacticMode.Cases();
            } else {
              tacticMode.CasesEnv(ToDafnyString(envVar ?? ""), ToDafnyString(newNameLeft ?? ""),
                ToDafnyString(newNameRight ?? ""));
            }
          } else if (tactic is RecallEnv {Name: var recallVar}) {
            tacticMode.UseHypothesis(ToDafnyString(recallVar ?? ""));
          } else if (tactic is Rename {OldName: var oldName, NewName: var newName}) {
            tacticMode.Rename(ToDafnyString(oldName ?? ""), ToDafnyString(newName ?? ""));
          }
          currentState = FromDafnyString(tacticMode.proofState._ToString());
          currentState = currentState == "" ? "QED" : currentState;
          reporter.Info(MessageSource.Verifier, tactic.TokenCloseParens, currentState);
        }

        if (tacticMode.proofState.is_Sequents &&
            tacticMode.proofState.dtor_sequents.is_SequentNil) {
          // Success !
          provenByAlcor = true;
          msg = "Proved by the tactics";
        }
      }

      if (!provenByAlcor) { // Automatic attempt
        // Attempt to prove it using Alcor. If so, we emit an assumption in Boogie
        var result = Alcor.__default.DummyProofFinder(
          new Expr_Imp(Environment.ToExpr(),
            alcorExpression));
        provenByAlcor = result.is_Success;
        if (provenByAlcor) {
          var expr = _IExprToString(result.dtor_value.dtor__0);
          var proof = _IProofProgramToString(result.dtor_value.dtor__1);
          msg = "Alcor automatically proved that " + expr + " by\n" + proof;
        } else {
          msg = FromDafnyString(result.dtor_msg);
        }
      }

      return provenByAlcor;
    }
  }
}