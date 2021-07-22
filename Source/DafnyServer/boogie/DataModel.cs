// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Boogie.ModelViewer
{
  public class ViewOptions
  {
    // 0 - Normal
    // 1 - Expert
    // 2 - Everything
    // 3 - Include the kitchen sink
    public int ViewLevel = 1;
    public bool DebugMode;
  }

  // sync with Main.categoryBrushes!
  public enum NodeCategory
  {
    Local,
    PhysField,
    SpecField,
    MethodologyProperty,
    UserFunction,
    Maplet
  }

  public class SourceViewState
  {
    public string Header;
    public string RichTextContent;
    public int Location;
  }

  public abstract class DisplayNode
  {
    protected EdgeName name;
    protected Model.Element element;
    protected LanguageModel langModel;
    protected List<DisplayNode> children;

    public DisplayNode(LanguageModel model, EdgeName n, Model.Element elt)
    {
      langModel = model;
      name = n;
      element = elt;
    }
    public NodeCategory Category { get; set; }

    public IEnumerable<DisplayNode> Children
    {
      get
      {
        if (children == null)
        {
          children = new List<DisplayNode>();
          ComputeChildren();
        }
        return children;
      }
    }

    protected virtual void ComputeChildren()
    {
    }

    public string Name => name.ToString();

    private string shortName;

    public string ShortName
    {
      get {
        if (shortName != null)
          return shortName;
        return name.ToString();
      }
      set => shortName = value;
    }

    public Model.Element Element => element;

    public string Value
    {
      get
      {
        if (element == null)
          return "";
        return langModel.CanonicalName(element);
      }
    }
  }

  public static class Util
  {
    public static void Assert(bool cond)
    {
      if (!cond) throw new Exception("assertion violation");
    }

    public static string Concat(this IEnumerable<string> strs, string sep)
    {
      var res = new StringBuilder();
      foreach (var e in strs)
        res.Append(e).Append(sep);
      if (res.Length > 0)
        res.Length -= sep.Length;
      return res.ToString();
    }

    public static IEnumerable<T> Empty<T>() { yield break; }
    
    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp, Func<S, T> conv)
    {
      foreach (var s in inp) yield return conv(s);
    }
  }

}
