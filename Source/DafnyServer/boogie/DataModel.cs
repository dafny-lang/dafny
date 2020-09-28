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

  public interface ILanguageProvider
  {
    bool IsMyModel(Model m);
    ILanguageSpecificModel GetLanguageSpecificModel(Model m, ViewOptions opts);
  }

  public interface ILanguageSpecificModel
  {
    string CanonicalName(Model.Element elt);

    Model.Element FindElement(string canonicalName);

    string PathName(IEnumerable<IDisplayNode> path);

    IEnumerable<IState> States { get; }

    // This function is given IDisplayNode possibly from different states.
    IEnumerable<string> SortFields(IEnumerable<IDisplayNode> fields);
  }

  public class SourceViewState
  {
    public string Header;
    public string RichTextContent;
    public int Location;
  }

  public interface IState
  {
    string Name { get; }
    SourceViewState ShowSource();
    IEnumerable<IDisplayNode> Nodes { get; }
  }

  public interface IDisplayNode
  {
    /// <summary>
    ///  Used for indexing the state tree.
    /// </summary>
    string Name { get; }

    string ShortName { get; }

    NodeCategory Category { get; }
    string Value { get; }
    string ToolTip { get; }

    int ViewLevel { get; }

    /// <summary>
    /// Used to determine aliasing. Can be null.
    /// </summary>
    Model.Element Element { get; }

    IEnumerable<Model.Element> References { get; }

    IEnumerable<IDisplayNode> Children { get; }

    object ViewSync { get; set; }
  }


  public class TopState : IState
  {
    protected IDisplayNode[] children;
    protected string name;

    public TopState(string name, IEnumerable<IDisplayNode> nodes)
    {
      this.name = name;
      children = nodes.ToArray();
    }

    public string Name
    {
      get { return name; }
    }

    public IEnumerable<IDisplayNode> Nodes
    {
      get { return children; }
    }


    public SourceViewState ShowSource()
    {
      return null;
    }

  }

  public abstract class DisplayNode : IDisplayNode
  {
    protected EdgeName name;
    protected Model.Element element;
    protected ILanguageSpecificModel langModel;
    protected List<IDisplayNode> children;

    public DisplayNode(ILanguageSpecificModel model, string n, Model.Element elt)
      : this(model, new EdgeName(n), elt) { }

    public DisplayNode(ILanguageSpecificModel model, EdgeName n, Model.Element elt)
    {
      langModel = model;
      name = n;
      element = elt;
    }

    public virtual string ToolTip
    {
      get { return null; }
    }

    public virtual int ViewLevel { get; set; }
    public virtual NodeCategory Category { get; set; }

    public virtual IEnumerable<IDisplayNode> Children
    {
      get
      {
        if (children == null)
        {
          children = new List<IDisplayNode>();
          ComputeChildren();
        }
        return children;
      }
    }

    protected virtual void ComputeChildren()
    {
    }

    public object ViewSync { get; set; }

    public virtual string Name
    {
      get { return name.ToString(); }
    }

    private string shortName;

    public virtual string ShortName
    {
      get
      {
        if (shortName != null)
        {
          return shortName;
        }
        else
        {
          return name.ToString();
        }
      }
      set
      {
        shortName = value;
      }
    }

    public virtual Model.Element Element
    {
      get { return element; }
    }

    public virtual string Value
    {
      get
      {
        if (element == null)
          return "";
        return langModel.CanonicalName(element);
      }
    }

    public virtual IEnumerable<Model.Element> References
    {
      get
      {
        foreach (var r in name.Dependencies)
          yield return r;
        if (element != null)
          yield return element;
      }
    }
  }

  public class ContainerNode<T> : DisplayNode
  {
    protected Func<T, IDisplayNode> convert;
    protected IEnumerable<T> data;

    public ContainerNode(EdgeName name, Func<T, IDisplayNode> convert, IEnumerable<T> data) : base(null, name, null)
    {
      this.convert = convert;
      this.data = data;
    }

    public ContainerNode(string name, Func<T, IDisplayNode> convert, IEnumerable<T> data)
      : this(new EdgeName(name), convert, data)
    {
    }

    protected override void ComputeChildren()
    {
      foreach (var f in data)
      {
        var res = convert(f);
        if (res != null)
          children.Add(res);
      }
    }
  }


  public static class Util
  {
    public static void Assert(bool cond)
    {
      if (!cond) throw new System.Exception("assertion violation");
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

    public static IEnumerable<T> Singleton<T>(T e) { yield return e; }

    public static IEnumerable<T> Concat1<T>(this IEnumerable<T> s, T e) { return s.Concat(Singleton(e)); }

    public static IEnumerable<T> Map<S, T>(this IEnumerable<S> inp, Func<S, T> conv)
    {
      foreach (var s in inp) yield return conv(s);
    }

    public static void Iter<T>(this IEnumerable<T> inp, Action<T> fn)
    {
      foreach (var s in inp) fn(s);
    }

    public static void AddRange<T>(this HashSet<T> st, IEnumerable<T> elts)
    {
      foreach (var e in elts) st.Add(e);
    }

    public static T OrElse<T>(T a, T b)
      where T : class
    {
      if (a != null) return a;
      return b;
    }

    public static S GetWithDefault<T, S>(this Dictionary<T, S> dict, T key, S defl)
    {
      S r;
      if (dict.TryGetValue(key, out r))
        return r;
      return defl;
    }
  }

}
