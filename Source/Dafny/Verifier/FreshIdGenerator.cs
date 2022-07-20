using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny {
  public class FreshIdGenerator {
    string tipString;  // a string representation of Tip
    int tipChildrenCount = 0;
    readonly Stack<Dictionary<string, int>> prefixToCountStack = new();  // invariant PrefixToCount_Stack.Count == Tip.Count

    public /*spec public*/ readonly Stack<int> Tip = new();

    public void Push() {
      Tip.Push(tipChildrenCount);
      tipChildrenCount = 0;
      tipString = ComputeTipString();
      prefixToCountStack.Push(new());
    }

    public void Pop() {
      Contract.Requires(Tip.Count > 0);
      int k = Tip.Pop();
      tipChildrenCount = k + 1;
      tipString = ComputeTipString();
      prefixToCountStack.Pop();
    }

    string ComputeTipString() {
      return Tip.Any() ? string.Join('_', Tip.Reverse().Select(t => t.ToString())) : null;
    }

    readonly string commonPrefix = "";

    public FreshIdGenerator() {
      prefixToCountStack.Push(new());
    }

    private FreshIdGenerator(string commonPrefix) : this() {
      this.commonPrefix = commonPrefix;
    }

    public void Reset() {
      var prefixToCount = prefixToCountStack.Peek();
      lock (prefixToCount) {
        prefixToCount.Clear();
      }
    }

    public string FreshId(string prefix) {
      return commonPrefix + prefix + FreshNumericId(prefix);
    }

    public FreshIdGenerator NestedFreshIdGenerator(string prefix) {
      return new(FreshId(prefix));
    }

    public string FreshNumericId(string prefix = "") {
      var prefixToCount = prefixToCountStack.Peek();
      lock (prefixToCount) {
        if (!prefixToCount.TryGetValue(prefix, out var old)) {
          old = 0;
        }
        prefixToCount[prefix] = old + 1;
        return tipString == null ? old.ToString() : tipString + "_" + old.ToString();
      }
    }
  }
}