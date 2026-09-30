// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Program = Microsoft.Boogie.Program;
using Substituter = Microsoft.Boogie.Substituter;
using Token = Microsoft.Boogie.Token;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail for each requires statement from the specification
  /// </summary>
  public class SpecBasedModifier : ProgramModifier {
    private readonly Modifications modifications;

    private Implementation /*?*/
      implementation; // the implementation currently traversed

    private Program /*?*/
      program; // the original program

    public SpecBasedModifier(Modifications modifications) {
      this.modifications = modifications;
    }

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      return VisitProgram(p);
    }

    private IEnumerable<ProgramModification> VisitImplementation(
      Implementation node) {
      implementation = node;
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        yield break;
      }

      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : [implementation.VerboseName];

      var entryBlock = node.Blocks.FirstOrDefault();
      if (entryBlock == null) {
        yield break;
      }

      var state = Utils.GetBlockId(entryBlock, DafnyInfo.Options);
      if (state == null) {
        yield break;
      }

      var procedure = implementation.Proc;
      var substMap = new Dictionary<Variable, Expr>();

      for (int i = 0; i < procedure.InParams.Count; i++) {
        substMap[procedure.InParams[i]] = new IdentifierExpr(Token.NoToken, implementation.InParams[i]);
      }

      for (int i = 0; i < procedure.OutParams.Count; i++) {
        substMap[procedure.OutParams[i]] = new IdentifierExpr(Token.NoToken, implementation.OutParams[i]);
      }

      var subst = Substituter.SubstitutionFromDictionary(substMap);

      string baseMethodName = implementation.VerboseName.Split(" ")[0];

      var reqClauses = procedure.Requires
        .Where(r => IsUserSpec(r.Condition))
        .Select(r => Substituter.Apply(subst, r.Condition))
        .ToList();

      var ensClauses = procedure.Ensures
        .Where(e => IsUserSpec(e.Condition))
        .Select(e => Substituter.Apply(subst, e.Condition))
        .ToList();

      var reqDnfCombs = DafnyInfo.Options.TestGenOptions.Fdnf
        ? EcpEngine.CalculateAllCombinations(reqClauses)
        : EcpEngine.CalculateSafeCombinations(reqClauses);
      var ensDnfCombs = DafnyInfo.Options.TestGenOptions.Fdnf
        ? EcpEngine.CalculateAllCombinations(ensClauses)
        : EcpEngine.CalculateSafeCombinations(ensClauses);

      int specTestIndex = 0;

      foreach (var preComb in reqDnfCombs) {
        foreach (var postComb in ensDnfCombs) {
          var baseComb = new List<Expr>(preComb);
          baseComb.AddRange(postComb);

          if (EcpEngine.FindContradiction(baseComb, out var constraints)) {
            continue;
          }

          var testCombs = new List<List<Expr>>();

          testCombs.Add(baseComb);

          if (DafnyInfo.Options.TestGenOptions.Bva != null) {
            List<Variable> allParams = [.. implementation.InParams, .. implementation.OutParams];
            var bvaCombs = EcpEngine.CalculateBva(allParams, constraints, program, (int)DafnyInfo.Options.TestGenOptions.Bva);

            foreach (var bva in bvaCombs) {
              var currentBvaComb = new List<Expr>(baseComb) { bva };
              testCombs.Add(currentBvaComb);
            }
          }

          foreach (var finalComb in testCombs) {
            string uniqueStateId = $"SpecComb_{baseMethodName}_{specTestIndex}";
            var captureStateAttr = new QKeyValue(new Token(), $"captureState_{baseMethodName}_{specTestIndex}",
              new List<object> { uniqueStateId });
            var captureAssumeCmd = new AssumeCmd(new Token(), Expr.True, captureStateAttr);

            var andExpr = EcpEngine.ConjoinExprs(finalComb);

            EcpEngine.FixTypes(andExpr);

            entryBlock.Cmds.Add(captureAssumeCmd);
            entryBlock.Cmds.Add(new AssumeCmd(new Token(), andExpr));
            entryBlock.Cmds.Add(new AssertCmd(new Token(), Expr.False));

            var targetStates = Utils.AllBlockIds(entryBlock, DafnyInfo.Options)
              .Where(id => id != null && id.Contains(uniqueStateId))
              .ToHashSet();

            var record = modifications.GetProgramModification(program, implementation,
              targetStates,
              testEntryNames, $"{baseMethodName}_{specTestIndex++} (spec)");

            yield return record;

            var index = entryBlock.Cmds.FindIndex(cmd =>
              cmd is AssumeCmd assumeCmd && assumeCmd.Attributes! is QKeyValue keyValue &&
              keyValue.Key.Equals(captureStateAttr.Key));
            if (index != -1) {
              entryBlock.Cmds.RemoveRange(index, 3);
            }
          }
        }
      }
    }

    private IEnumerable<ProgramModification> VisitProgram(Program node) {
      program = node;
      var implementations = node.Implementations.ToList();
      foreach (var implementation in implementations) {
        foreach (var modification in VisitImplementation(implementation)) {
          yield return modification;
        }
      }
    }

    private bool IsUserSpec(Expr expr) {
      string str = expr.ToString();

      if (str.Contains("$Heap") || str.Contains("$Tick") || str.Contains("alloc")) {
        return false;
      }

      if (expr is LiteralExpr lit && lit.Val is bool b && b) {
        return false;
      }

      return true;
    }
  }
}