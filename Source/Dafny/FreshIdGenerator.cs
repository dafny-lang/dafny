//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny
{
  public class FreshIdGenerator
  {
    Dictionary<string, int> PrefixToCount = new Dictionary<string, int>();

    public /*spec public*/ readonly Stack<int> Tip = new Stack<int>();
    string tipString;  // a string representation of Tip
    int tipChildrenCount = 0;
    readonly Stack<Dictionary<string, int>> PrefixToCount_Stack = new Stack<Dictionary<string, int>>();  // invariant PrefixToCount_Stack.Count == Tip.Count
    public void Push() {
      Tip.Push(tipChildrenCount);
      tipChildrenCount = 0;
      tipString = ComputeTipString();
      PrefixToCount_Stack.Push(PrefixToCount);
      PrefixToCount = new Dictionary<string, int>();
    }
    public void Pop() {
      Contract.Requires(Tip.Count > 0);
      int k = Tip.Pop();
      tipChildrenCount = k + 1;
      tipString = ComputeTipString();
      PrefixToCount = PrefixToCount_Stack.Pop();
    }
    string ComputeTipString() {
      string s = null;
      foreach (var k in Tip) {
        if (s == null) {
          s = k.ToString();
        } else {
          s = k.ToString() + "_" + s;
        }
      }
      return s;
    }

    readonly string CommonPrefix = "";

    public FreshIdGenerator()
    {
    }

    private FreshIdGenerator(string commonPrefix)
    {
      CommonPrefix = commonPrefix;
    }

    public void Reset()
    {
      lock (PrefixToCount)
      {
        PrefixToCount.Clear();
      }
    }

    public string FreshId(string prefix)
    {
      return CommonPrefix + prefix + FreshNumericId(prefix);
    }

    public FreshIdGenerator NestedFreshIdGenerator(string prefix)
    {
      return new FreshIdGenerator(FreshId(prefix));
    }

    public string FreshNumericId(string prefix = "")
    {
      lock (PrefixToCount)
      {
        int old;
        if (!PrefixToCount.TryGetValue(prefix, out old)) {
          old = 0;
        }
        PrefixToCount[prefix] = old + 1;
        return tipString == null ? old.ToString() : tipString + "_" + old.ToString();
      }
    }
  }
}
