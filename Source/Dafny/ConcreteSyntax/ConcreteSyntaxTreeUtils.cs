using System.Diagnostics.Contracts;
using System.Text;

namespace Microsoft.Dafny
{
  public static class ConcreteSyntaxTreeUtils
  {
    public static string Repeat(string template, int times, string separator = "")
    {
      Contract.Requires(times >= 0);
      
      var builder = new StringBuilder();
      string sep = "";
      for (int i = 0; i < times; i++) {
        builder.Append(sep);
        builder.Append(string.Format(template, i));
        sep = separator;
      }

      return builder.ToString();
    }
    
    public static ConcreteSyntaxTree BracketList(params ICanRender[] elements)
    {
      var result = List(elements);
      result.Prepend<LineSegment>("<");
      result.Write(">");
      return result;
    }

    public static ConcreteSyntaxTree ParensList(params ICanRender[] elements)
    {
      var result = List(elements);
      result.Prepend<LineSegment>("(");
      result.Write(")");
      return result;
    }

    public static ConcreteSyntaxTree List(params ICanRender[] elements)
    {
      var result = new ConcreteSyntaxTree();
      if (elements.Length > 0) {
        result.Append(elements[0]);
        for (int i = 1; i < elements.Length; i++) {
          result.Write(", ");
          result.Append(elements[i]);
        }
      }
      return result;
    }
    public static ConcreteSyntaxTree ExprBlock(out ConcreteSyntaxTree body, string header = "", string footer = "") {
      return Block(out body, header, footer, BraceStyle.Space, BraceStyle.Nothing);
    }
    
    public static ConcreteSyntaxTree Block(out ConcreteSyntaxTree body, string header = "", string footer = "",
      BraceStyle open = BraceStyle.Space,
      BraceStyle close = BraceStyle.Newline)
    {
      var outer = new ConcreteSyntaxTree();
      
      outer.Write(header);
      switch (open) {
        case BraceStyle.Space:
          outer.Write(" ");
          break;
        case BraceStyle.Newline:
          outer.WriteLine();
          break;
      }
            
      outer.WriteLine("{");
      body = outer.Fork(1);
      outer.Write("}");
            
      if (footer != "") {
        outer.Write(footer);
      }
      switch (close) {
        case BraceStyle.Space:
          outer.Write(" ");
          break;
        case BraceStyle.Newline:
          outer.WriteLine();
          break;
      }
      return outer;
    }
  }
}