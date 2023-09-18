using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Numerics;
using AlcorProofKernel;
using AlcorTacticProofChecker;
using Dafny;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

partial class Translator {
  internal record AlcorAssumptions(Env Environment, ImmutableList<Tactic> Tactics) {
    public AlcorAssumptions WithEnv(Expression assumption, ExpressionTranslator etran, string name = null) {
      var assumptionAlcor = etran.TrExprAlcor(assumption, out var errorMessage);
      if (assumptionAlcor != null) {
        return WithEnv(assumptionAlcor, name);
      } else {
        return this;
      }
    }

    public AlcorAssumptions WithEnv(_IExpr alcorExpression, string name = null) {
      var label = 
        Environment.FreshVar(ToDafnyString(name ?? "h"));

      return new AlcorAssumptions(new Env_EnvCons(
        label, alcorExpression, Environment
      ), Tactics);
    }

    public AlcorAssumptions WithAssertedExpr(_IExpr alcorExpression, [CanBeNull] string labelString) {
      var label = 
        Environment.FreshVar(ToDafnyString(labelString ?? "h"));
      return new AlcorAssumptions(
        new Env_EnvCons(
          label, alcorExpression, Environment),
        ImmutableList<Tactic>.Empty);
    }
    
    public AlcorAssumptions WithAssumedExpr(_IExpr alcorExpression, [CanBeNull] string labelString) {
      var label = 
        Environment.FreshVar(ToDafnyString(labelString ?? "h"));
      return new AlcorAssumptions(
        new Env_EnvCons(
          label, alcorExpression, Environment),
        Tactics);
    }

    public AlcorAssumptions WithTactics(IEnumerable<Tactic> tactics) {
      return new AlcorAssumptions(Environment, Tactics.AddRange(tactics));
    }

    public bool Prove(_IExpr alcorExpression, ExpressionTranslator etran, ErrorReporter reporter, out string msg) {
      var provenByAlcor = false;
      msg = "";
      if (Tactics.Any()) {
        // First we execute reveal tactics that add functions in scope
        var environment = Environment;
        foreach (var tactic in Tactics) {
          if (tactic is RevealFunction {Function: var function}) {
            var newEnvElem = ToAxiom(function, etran, out string errorMessage);
            if (newEnvElem != null) {
              environment = new Env_EnvCons(ToDafnyString(function.Name),
                newEnvElem, environment
              );
            } else {
              reporter.Error(MessageSource.Verifier, tactic.Token, errorMessage);
            }
          }
        }

        // We execute the tactics that were provided by the user
        var tacticMode = new TacticMode();
        tacticMode.__ctor(alcorExpression, environment);
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
          } else if (tactic is RevealFunction {Function: var function}) {
            var newEnvElem = ToAxiom(function, etran, out string errorMessage);
            if (newEnvElem != null) {
              tacticMode._env = new Env_EnvCons(ToDafnyString(function.Name),
                newEnvElem, tacticMode._env
              );
            } else {
              reporter.Error(MessageSource.Verifier, tactic.Token, errorMessage);
            }
          } else if (tactic is ForallElim {Name: var name2, Expr: var expr, NewName: var newName2}) {
            var replaced = etran.TrExprAlcor(expr, out var errorMessage);
            if (replaced == null) {
              reporter.Error(MessageSource.Verifier, tactic.Token, errorMessage);
            } else {
              var exprAlcor = etran.TrExprAlcor(expr, out var errorMessage2);
              if (exprAlcor != null) {
                tacticMode.ForallElim(ToDafnyString(name2), exprAlcor,
                  newName2 != null ? ToDafnyString(newName2) : null);
              } else {
                reporter.Error(MessageSource.Verifier, expr.Tok, errorMessage2);
              }
            }
          } else if (tactic is Simplify {Name: var name3}) {
            tacticMode.Simplify(name3 != null ? ToDafnyString(name3) : null, BigInteger.Zero);
          } else if (tactic is Definition {InName: var inName, DefinitionName: var definitionName}) {
            tacticMode.Definition(ToDafnyString(inName), ToDafnyString(definitionName));
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

      if (!provenByAlcor && alcorExpression != null) { // Automatic attempt
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

    private _IExpr ToAxiom(Function function, ExpressionTranslator etran, out string errorMessage) {
      var body = function.Body;
      errorMessage = "";
      _IExpr bodyAlcor = etran.TrExprAlcor(body, out errorMessage);
      if (bodyAlcor == null) {
        errorMessage = "Could not transform the body of " + function.Name + " into Alcor expression because " + errorMessage;
        return null;
      }

      _IExpr term = new Expr_Var(
        new Identifier(ToDafnyString(function.Name), BigInteger.Zero, ToDafnyString(""))
      );
      
      foreach (var formal in function.Formals) {
        term = new Expr_App(term, new Expr_Var(etran.TrIdentifierAlcor(formal)));
      }

      bodyAlcor = new Expr_Var(new Identifier(ToDafnyString("=="), BigInteger.Zero, ToDafnyString("")))
        .apply2(term, bodyAlcor);

      foreach (var formal in function.Formals.ToImmutableList().Reverse()) {
        var id = etran.TrIdentifierAlcor(formal);
        bodyAlcor = new Expr_Forall(new Expr_Abs(id, bodyAlcor));
      }

      errorMessage = "";
      return bodyAlcor;
    }
  }
}