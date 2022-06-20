using System.Collections.Generic;
using Microsoft.Boogie;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail when a particular path is taken
  /// </summary>
  public class PathBasedModifier : ProgramModifier {

    // prefix given to variables indicating whether or not a block was visited
    private const string BlockVarNamePrefix = "$$visited$$_";
    private List<Path> paths = new();

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      paths = new List<Path>();
      var result = new List<ProgramModification>();
      p = VisitProgram(p); // populates paths
      foreach (var path in paths) {
        path.AssertPath();
        result.Add(new ProgramModification(p,
          ImplementationToTarget?.VerboseName ?? path.Impl.VerboseName));
        path.NoAssertPath();
      }
      return result;
    }

    /// <summary>
    /// Insert variables to register which blocks are visited
    /// and then populate the paths field.
    /// </summary>
    public override Implementation VisitImplementation(Implementation node) {
      if (!ImplementationIsToBeTested(node)) {
        return node;
      }
      InitBlockVars(node);
      var blockNameToId = GetIdToBlock(node);
      GeneratePaths(node,
        blockNameToId,
        node.Blocks[0],
        new HashSet<int>(),
        new List<int>());
      return node;
    }

    /// <summary>
    /// Create a map from block ids (aka labels) to blocks themselves
    /// </summary>
    private static Dictionary<string, Block> GetIdToBlock(Implementation impl) {
      var result = new Dictionary<string, Block>();
      foreach (var block in impl.Blocks) {
        result[block.Label] = block;
      }
      return result;
    }

    /// <summary>
    /// Modify implementation by adding variables indicating whether or not
    /// certain blocks were visited.
    /// </summary>
    private static void InitBlockVars(Implementation node) {
      foreach (var block in node.Blocks) {
        var var = BlockVarNamePrefix + block.UniqueId;
        // variable declaration:
        node.LocVars.Add(new LocalVariable(new Token(),
          new TypedIdent(new Token(), var, Type.Bool)));
        // initialization:
        block.cmds.Insert(0, GetCmd($"{var} := true;", returns: $"{var}:bool"));
        // set variable to true when visiting a block
        node.Blocks[0].cmds.Insert(0, GetCmd(
          $"var {var}:bool; {var} := false;"));
      }
    }

    /// <summary>
    /// Populate paths field with paths generated for the given implementation
    /// </summary>
    /// <param name="impl">implementation to generate paths for</param>
    /// <param name="idToBlock">maps block ids to blocks</param>
    /// <param name="block">block with which to start AST traversal</param>
    /// <param name="currSet">set of block already inside the path</param>
    /// <param name="currList">the blocks forming the path</param>
    private void GeneratePaths(Implementation impl,
      Dictionary<string, Block> idToBlock, Block block,
      HashSet<int> currSet, List<int> currList) {
      if (currSet.Contains(block.UniqueId)) {
        return;
      }

      // if the block contains a return command, it is the last one in the path:
      if (block.TransferCmd is ReturnCmd) {
        paths.Add(new Path(impl, currList, block));
        return;
      }

      // otherwise, each goto statement presents a new path to take:
      currSet.Add(block.UniqueId);
      currList.Add(block.UniqueId);
      var gotoCmd = block.TransferCmd as GotoCmd;
      foreach (var b in gotoCmd?.labelNames ?? new List<string>()) {
        GeneratePaths(impl, idToBlock, idToBlock[b], currSet, currList);
      }
      currList.RemoveAt(currList.Count - 1);
      currSet.Remove(block.UniqueId);
    }

    private class Path {

      public readonly Implementation Impl;
      private readonly List<int> path; // indices of blocks along the path
      private readonly Block returnBlock; // block where the path ends

      internal Path(Implementation impl, IEnumerable<int> path, Block returnBlock) {
        Impl = impl;
        this.path = new List<int>();
        this.path.AddRange(path); // deepcopy is necessary here
        this.returnBlock = returnBlock;
      }

      internal void AssertPath() {
        if (path.Count == 0) {
          returnBlock.cmds.Add(GetCmd("assert false;"));
          return;
        }

        var vars = path.ConvertAll(x => BlockVarNamePrefix + x);
        var varsCond = string.Join("||", vars.ConvertAll(x => $"!{x}"));
        // The only purpose of varsIn is to make a call to GetCmd possible
        var varsIn = string.Join(", ", vars.ConvertAll(x => $"{x}:bool"));
        returnBlock.cmds.Add(GetCmd($"assert {varsCond};", varsIn));
      }

      internal void NoAssertPath() {
        returnBlock.cmds.RemoveAt(returnBlock.cmds.Count - 1);
      }
    }
  }
}