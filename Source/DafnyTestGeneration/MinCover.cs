using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Google.OrTools.Sat;
using Microsoft.Dafny;

namespace DafnyTestGeneration;

public static class MinCover {

  private static HashSet<Block> GetLoopHeads(Implementation implementation) {
    HashSet<Block> loopHeads = new();
    GetLoopHeadsHelper(implementation.Blocks[0], new(), loopHeads);
    return loopHeads;
  }

  private static void GetLoopHeadsHelper(Block block, HashSet<Block> visited,
    HashSet<Block> loopHeads) {
    visited.Add(block);
    if (block.TransferCmd is not GotoCmd gotoCmd) {
      return;
    }

    foreach (var successor in gotoCmd.labelTargets) {
      if (visited.Contains(successor)) {
        loopHeads.Add(successor);
      } else {
        GetLoopHeadsHelper(successor, visited, loopHeads);
      }
    }
  }

  public static HashSet<HashSet<Block>> GetMinCover(
    Implementation implementation, List<HashSet<Block>> infeasiblePaths,
    int minPaths) {

    // Initializing the problem
    CpModel model = new CpModel();
    var vars = new Dictionary<Block, BoolVar>[minPaths];
    for (int i = 0; i < vars.Length; i++) {
      vars[i] = new Dictionary<Block, BoolVar>();
      foreach (var block in implementation.Blocks) {
        vars[i][block] = model.NewBoolVar(i + "-" + block.UniqueId);
      }
    }

    // All blocks must be covered
    foreach (var block in implementation.Blocks) {
      model.AddBoolOr(vars.Select(path => path[block]));
    }

    // At least one predecessor for each block except the first
    for (int i = 1; i < implementation.Blocks.Count; i++) {
      var block = implementation.Blocks[i];
      foreach (var path in vars) {
        model.AddBoolOr(block.Predecessors.Select(p => path[p])
          .Append(path[block].Not()));
      }
    }

    // Exactly one successor for each non-loop-head, non-return block 
    var returnBlocks =
      implementation.Blocks.Where(block => block.TransferCmd is ReturnCmd);
    var loopHeads = GetLoopHeads(implementation);
    foreach (var block in implementation.Blocks) {
      if (block.TransferCmd is not GotoCmd gotoCmd) {
        continue; // this is a return block
      }
      foreach (var path in vars) {
        if (loopHeads.Contains(block)) {
          model.AddBoolOr(gotoCmd.labelTargets.Select(p => path[p])
            .Append(path[block].Not()));
        } else {
          model.Add(LinearExpr.Sum(gotoCmd.labelTargets.Select(p => path[p])) == 1).OnlyEnforceIf(path[block]);
        }
      }
    }

    // Exactly one return block per path
    foreach (var path in vars) {
      model.AddExactlyOne(returnBlocks.Select(block => path[block]));
    }

    // Infeasibility of certain paths
    foreach (var infeasiblePath in infeasiblePaths) {
      foreach (var path in vars) {
        model.AddBoolOr(infeasiblePath.Select(block => path[block].Not()));
      }
    }

    // Try solving the problem
    CpSolver solver = new CpSolver();
    CpSolverStatus status = solver.Solve(model);
    if ((status == CpSolverStatus.ModelInvalid ||
         status == CpSolverStatus.Unknown) &&
        DafnyOptions.O.TestGenOptions.Verbose) {
      Console.WriteLine("// Solver returned " + status + " status");
    }
    if (status == CpSolverStatus.ModelInvalid ||
        status == CpSolverStatus.Unknown ||
        status == CpSolverStatus.Infeasible) {
      if (minPaths >= implementation.Blocks.Count) {
        return new HashSet<HashSet<Block>>();
      }
      if (DafnyOptions.O.TestGenOptions.Verbose) {
        Console.WriteLine("// Increasing minimum to " + (minPaths + 1));
      }
      return GetMinCover(implementation, infeasiblePaths, minPaths + 1);
    }

    // Reconstruct and simplify the paths
    HashSet<HashSet<Block>> solution = new();
    HashSet<Block> coveredBlocks = new();
    foreach (var path in vars) {
      var solutionPath = new HashSet<Block>();
      foreach (var block in implementation.Blocks) {
        if (solver.BooleanValue(path[block]) &&
            !coveredBlocks.Contains(block)) {
          coveredBlocks.Add(block);
          solutionPath.Add(block);
        }
      }
      if (solutionPath.Count == 0 && DafnyOptions.O.TestGenOptions.Verbose) {
        Console.WriteLine("// Invalid SAT solution");
      }
      solution.Add(solutionPath);
    }
    return solution;
  }

}