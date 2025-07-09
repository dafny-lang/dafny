// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Program = Microsoft.Boogie.Program;
using Token = Microsoft.Boogie.Token;
using Type = Microsoft.Boogie.Type;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular path is taken
  /// </summary>
  public class PathBasedModifier : ProgramModifier {
    private readonly Modifications modifications;

    // prefix given to variables indicating whether or not a block was visited
    private const string BlockVarNamePrefix = "block";
    // Dafny will try to generate tests for paths through the program of increasingly greater length,
    // PathLengthStep determines the increments by which Dafny should increase maximum path length in-between attempts
    private const int PathLengthStep = 20;

    public PathBasedModifier(Modifications modifications) {
      this.modifications = modifications;
    }

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      var implementations = p.Implementations.ToList();
      foreach (var implementation in implementations) {
        if (!ImplementationIsToBeTested(implementation) ||
            !DafnyInfo.IsAccessible(implementation.VerboseName.Split(" ")[0])) {
          continue;
        }

        int pathLength = PathLengthStep;
        bool newPathsFound = true;
        // Consider paths of increasing length, pruning out infeasible sub-paths in the process:
        var blockToVariable = InitBlockVars(implementation);
        var firstBlock = implementation.Blocks[0]; // 
        while (newPathsFound) {
          List<Path> pathsToConsider = []; // paths without known unfeasible subpaths
          var totalPaths = 0;
          foreach (var path in GeneratePaths(implementation, pathLength - PathLengthStep, pathLength, blockToVariable, firstBlock)) {
            totalPaths++;
            var pathId = path.ToString(DafnyInfo.Options);
            if (pathLength <= PathLengthStep || !modifications.Values.Any(modification =>
                  pathId.StartsWith(modification.uniqueId) &&
                  modification.CounterexampleStatus == ProgramModification.Status.Failure)) {
              pathsToConsider.Add(path);
            }
          }
          newPathsFound = pathsToConsider.Count() != 0;
          if (DafnyInfo.Options.Verbose) {
            Console.Out.WriteLine(
              $"// Now considering paths of length {pathLength - PathLengthStep} to {pathLength} for {implementation.VerboseName}");
            Console.Out.WriteLine($"// Maximum number of feasible paths of this length is  {pathsToConsider.Count} out of {totalPaths} total");
          }
          foreach (var path in pathsToConsider) {
            path.AssertPath();
            var testEntryNames = Utils.DeclarationHasAttribute(path.Impl, TestGenerationOptions.TestInlineAttribute)
              ? TestEntries
              : [path.Impl.VerboseName];
            var programCopy = Utils.DeepCloneResolvedProgram(p, DafnyInfo.Options);
            yield return modifications.GetProgramModification(programCopy, path.Impl, [], testEntryNames,
              path.ToString(DafnyInfo.Options));
            path.NoAssertPath();
          }
          pathLength += PathLengthStep;
        }
      }
    }

    /// <summary>
    /// Modify implementation by adding variables indicating whether or not
    /// certain blocks were visited.
    /// </summary>
    private static Dictionary<Block, Variable> InitBlockVars(Implementation node) {
      var blockToVariable = new Dictionary<Block, Variable>();
      foreach (var block in node.Blocks) {
        var varName = BlockVarNamePrefix + block.UniqueId;
        // variable declaration:
        var variable = GetNewLocalVariable(node, Type.Bool, varName);
        // set variable to false when visiting a block
        block.Cmds.Insert(0, new AssignCmd(new Token(),
          new List<AssignLhs>() { new SimpleAssignLhs(new Token(), new IdentifierExpr(new Token(), variable)) },
          new List<Expr>() { new LiteralExpr(new Token(), false) }));
        blockToVariable[block] = variable;
        // initialization:
        node.Blocks[0].Cmds.Insert(0, new AssignCmd(new Token(),
          new List<AssignLhs>() { new SimpleAssignLhs(new Token(), new IdentifierExpr(new Token(), variable)) },
          new List<Expr>() { new LiteralExpr(new Token(), true) }));
      }
      return blockToVariable;
    }

    /// <summary>
    /// Iterate over paths through an implementation in a depth-first search fashion
    /// </summary>
    private IEnumerable<Path> GeneratePaths(Implementation impl, int minPathLength, int maxPathLength, Dictionary<Block, Variable> blockToVariable, Block firstBlock) {
      List<Block> currPath = []; // list of basic blocks along the current path
      // remember alternative paths that could have been taken at every goto: 
      List<List<Block>> otherGotos = [[]];
      // set of boolean variables indicating that blocks in currPath list have been visited:
      HashSet<Variable> currPathVariables = [];
      var block = firstBlock;
      while (block != null) {
        if ((block.TransferCmd is ReturnCmd && currPath.Count >= minPathLength) || currPath.Count == maxPathLength - 1) {
          yield return new Path(impl, currPathVariables.ToList(), [block],
            currPath.Append(block).ToList());
        } else {
          if (currPath.Count != 0 && ((GotoCmd)currPath.Last().TransferCmd).LabelTargets.Count != 1) {
            currPathVariables.Add(blockToVariable[block]); // only constrain the path if there is more than one goto
          }
          currPath.Add(block);
          otherGotos.Add([]);
          var gotoCmd = block.TransferCmd as GotoCmd;
          foreach (var nextBlock in gotoCmd?.LabelTargets ?? []) {
            if (currPathVariables.Contains(blockToVariable[nextBlock])) { // this prevents cycles
              continue;
            }
            otherGotos.Last().Add(nextBlock);
          }
          if (otherGotos.Last().Count > 0) {
            block = otherGotos.Last().First();
            continue;
          }
        }
        var options = otherGotos.Last();
        while (otherGotos.Count > 1 && options.Count <= 1) {
          currPathVariables.Remove(blockToVariable[currPath.Last()]);
          currPath.RemoveAt(currPath.Count - 1);
          otherGotos.RemoveAt(otherGotos.Count - 1);
          options = otherGotos.Last();
        }
        if (options.Count <= 1) {
          block = null;
          continue;
        }
        options.RemoveAt(0);
        block = options.First();
      }
    }

    private class Path {

      public readonly Implementation Impl;
      private readonly List<Variable> path; // flags for the blocks along the path
      private readonly List<Block> returnBlocks; // block(s) where the path ends
      private readonly List<Block> pathBlocks;

      internal Path(Implementation impl, IEnumerable<Variable> path, List<Block> returnBlocks, List<Block> pathBlocks) {
        Impl = impl;
        this.path = [];
        this.path.AddRange(path); // deepcopy is necessary here
        this.returnBlocks = returnBlocks;
        this.pathBlocks = pathBlocks;
      }

      public string ToString(DafnyOptions options) {
        return $"{Impl.VerboseName.Split(" ")[0]} path through " +
               $"{string.Join(",", pathBlocks.ConvertAll(block => Utils.GetBlockId(block, options) ?? block.UniqueId.ToString()))}";
      }

      /// <summary>
      /// Constructs a binary tree of disjunctions made up of <param name="clauses"></param>
      /// This limits the depth of the resulting AST and prevents stack overflow during verification for large trees
      /// </summary>
      private Expr ConstructDisjunction(List<Expr> clauses) {
        if (clauses.Count >= 2) {
          int mid = clauses.Count / 2;
          return new NAryExpr(new Token(),
            new BinaryOperator(new Token(), BinaryOperator.Opcode.Or),
            new List<Expr>() {
              ConstructDisjunction(clauses.GetRange(0, mid)),
              ConstructDisjunction(clauses.GetRange(mid, clauses.Count - mid))
            });
        }
        if (clauses.Count == 1) {
          return clauses[0];
        }
        return new LiteralExpr(new Token(), true);
      }

      internal void AssertPath() {
        foreach (var returnBlock in returnBlocks) {
          if (path.Count == 0) {
            returnBlock.Cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
            return;
          }
        }

        var condition =
          ConstructDisjunction(path.Select(variable => new IdentifierExpr(new Token(), variable) as Expr).ToList());

        foreach (var returnBlock in returnBlocks) {
          returnBlock.Cmds.Add(new AssertCmd(new Token(), condition));
        }
      }

      internal void NoAssertPath() {
        foreach (var returnBlock in returnBlocks) {
          returnBlock.Cmds.RemoveAt(returnBlock.Cmds.Count - 1);
        }
      }
    }
  }
}