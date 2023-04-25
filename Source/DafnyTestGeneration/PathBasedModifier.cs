#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular path is taken
  /// </summary>
  public class PathBasedModifier : ProgramModifier {
    private readonly Modifications modifications;

    // prefix given to variables indicating whether or not a block was visited
    private const string BlockVarNamePrefix = "block";
    private List<Path> paths = new();

    public PathBasedModifier(Modifications modifications) {
      this.modifications = modifications;
    }

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      paths = new List<Path>();
      VisitProgram(p); // populates paths
      foreach (var path in paths) {
        path.AssertPath();
        var name = TargetImplementationVerboseName ?? path.Impl.VerboseName;
        yield return modifications.GetProgramModification(p, path.Impl,
          new HashSet<int>(), new HashSet<string>(), name,
          $"{name.Split(" ")[0]}" + path.name);
        path.NoAssertPath();
      }
    }

    private void VisitProgram(Program node) {
      foreach (var implementation in node.Implementations) {
        VisitImplementation(implementation);
      }
    }

    /// <summary>
    /// Insert variables to register which blocks are visited
    /// and then populate the paths field.
    /// </summary>
    private void VisitImplementation(Implementation node) {
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        return;
      }
      var blockToVariable = InitBlockVars(node);
      GeneratePaths(node,
        blockToVariable,
        node.Blocks[0],
        new HashSet<Variable>(),
        new List<Variable>());
    }

    /// <summary>
    /// Modify implementation by adding variables indicating whether or not
    /// certain blocks were visited.
    /// </summary>
    internal static Dictionary<Block, Variable> InitBlockVars(Implementation node) {
      var blockToVariable = new Dictionary<Block, Variable>();
      foreach (var block in node.Blocks) {
        var varName = BlockVarNamePrefix + block.UniqueId;
        // variable declaration:
        var variable = GetNewLocalVariable(node, Type.Bool, varName);
        // set variable to false when visiting a block
        block.cmds.Insert(0, new AssignCmd(new Token(),
          new List<AssignLhs>() { new SimpleAssignLhs(new Token(), new IdentifierExpr(new Token(), variable)) },
          new List<Expr>() { new LiteralExpr(new Token(), false) }));
        blockToVariable[block] = variable;
        // initialization:
        node.Blocks[0].cmds.Insert(0, new AssignCmd(new Token(),
          new List<AssignLhs>() { new SimpleAssignLhs(new Token(), new IdentifierExpr(new Token(), variable)) },
          new List<Expr>() { new LiteralExpr(new Token(), true) }));
      }
      return blockToVariable;
    }

    /// <summary>
    /// Populate paths field with paths generated for the given implementation
    /// </summary>
    /// <param name="impl">implementation to generate paths for</param>
    /// <param name="blockToVariable"> maps block to flag variables</param>
    /// <param name="block">block with which to start AST traversal</param>
    /// <param name="currSet">set of block already inside the path</param>
    /// <param name="currList">the blocks forming the path</param>
    private void GeneratePaths(Implementation impl,
      Dictionary<Block, Variable> blockToVariable, Block block,
      HashSet<Variable> currSet, List<Variable> currList) {
      if (currSet.Contains(blockToVariable[block])) {
        return;
      }

      // if the block contains a return command, it is the last one in the path:
      if (block.TransferCmd is ReturnCmd) {
        paths.Add(new Path(impl, currList, block, 
          $"(path through {string.Join(",", currList)},{blockToVariable[block]})"));
        return;
      }

      // otherwise, each goto statement presents a new path to take:
      currSet.Add(blockToVariable[block]);
      currList.Add(blockToVariable[block]);
      var gotoCmd = block.TransferCmd as GotoCmd;
      foreach (var b in gotoCmd?.labelTargets ?? new List<Block>()) {
        GeneratePaths(impl, blockToVariable, b, currSet, currList);
      }
      currList.RemoveAt(currList.Count - 1);
      currSet.Remove(blockToVariable[block]);
    }

    internal class Path {

      internal string name;
      public readonly Implementation Impl;
      public readonly List<Variable> path; // flags for the blocks along the path
      private readonly List<Block> returnBlocks; // block(s) where the path ends

      internal Path(Implementation impl, IEnumerable<Variable> path, Block returnBlock, string name)
        : this(impl, path, new List<Block>() { returnBlock }, name) {
      }

      internal Path(Implementation impl, IEnumerable<Variable> path, List<Block> returnBlocks, string name) {
        Impl = impl;
        this.path = new();
        this.path.AddRange(path); // deepcopy is necessary here
        this.returnBlocks = returnBlocks;
        this.name = name;
      }

      internal void AssertPath() {
        foreach (var returnBlock in returnBlocks) {
          if (path.Count == 0) {
            returnBlock.cmds.Add(new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));
            return;
          }
        }

        Expr condition = new IdentifierExpr(new Token(), path[0]);
        for (int i = 1; i < path.Count(); i++) {
          condition = new NAryExpr(new Token(),
            new BinaryOperator(new Token(), BinaryOperator.Opcode.Or),
            new List<Expr>()
              { condition, new IdentifierExpr(new Token(), path[i]) });
        }

        foreach (var returnBlock in returnBlocks) {
          returnBlock.cmds.Add(new AssertCmd(new Token(), condition));
        }
      }

      internal void NoAssertPath() {
        foreach (var returnBlock in returnBlocks) {
          returnBlock.cmds.RemoveAt(returnBlock.cmds.Count - 1);
        }
      }
    }
  }
}