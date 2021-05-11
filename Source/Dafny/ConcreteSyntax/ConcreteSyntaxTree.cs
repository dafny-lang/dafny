using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text;

namespace Microsoft.Dafny
{
  public class ConcreteSyntaxTree : TextWriter, ICanRender {
        
    public ConcreteSyntaxTree(int relativeIndent = 0) {
      RelativeIndentLevel = relativeIndent;
    }

    public readonly int RelativeIndentLevel;

    private readonly IList<ICanRender> _nodes = new List<ICanRender>();

    public override void Write(string format, object arg0)
    {
      Write(string.Format(format, arg0));
    }

    public ConcreteSyntaxTree Fork(int relativeIndent = 0)
    {
      var result = new ConcreteSyntaxTree(relativeIndent);
      _nodes.Add(result);
      return result;
    }

    public void Append(ICanRender node) {
      Contract.Requires(node != null);
      _nodes.Add(node);
    }

    public override void Write(object value) {
      Write(value.ToString());
    }
        
    public override void Write(string value) {
      _nodes.Add(new LineSegment(value));
    }

    public override void WriteLine(string format, params object[] args)
    {
      WriteLine(string.Format(format, args));
    }

    public override Encoding Encoding => Encoding.Default;

    public override void WriteLine(string value)
    {
      Write(value);
      WriteLine();
    }
        
    public override void WriteLine()
    {
      _nodes.Add(new NewLine());
    }

    public override void Write(string format, params object[] args)
    {
      Write(string.Format(format, args));
    }
        
    public override void Write(char value) {
      Write(new string(value, 1));
    }

    public void RepeatWrite(int times, string template, string separator) {
      Contract.Requires(1 <= times);
      Contract.Requires(template != null);
      Contract.Requires(separator != null);
      string sep = "";
      for (int i = 0; i < times; i++) {
        Write(sep);
        Write(template, i);
        sep = separator;
      }
    }

    // ----- Nested blocks ------------------------------

    public ConcreteSyntaxTree AppendChildInParenthesis()
    {
      var result = new ConcreteSyntaxTree();
      Write("(");
      Append(result);
      Write(")");
      return result;
    }
        
    public enum BraceStyle { Nothing, Space, Newline }
        
    public ConcreteSyntaxTree NewBlock(string header, string/*?*/ footer = null,
      BraceStyle open = BraceStyle.Space,
      BraceStyle close = BraceStyle.Newline) {
      Contract.Requires(header != null);
      Write(header);
            
      switch (open) {
        case BraceStyle.Space:
          Write(" ");
          break;
        case BraceStyle.Newline:
          WriteLine();
          break;
      }
            
      WriteLine("{");
      var result = Fork(1);
      Write("}");
            
      if (footer != null) {
        Write(footer);
      }
      switch (close) {
        case BraceStyle.Space:
          Write(" ");
          break;
        case BraceStyle.Newline:
          WriteLine();
          break;
      }
      return result;
    }

    public ConcreteSyntaxTree NewNamedBlock(string headerFormat, params object[] headerArgs)
    {
      Contract.Requires(headerFormat != null);
      return NewBlock(string.Format(headerFormat, headerArgs), null);
    }

    public ConcreteSyntaxTree NewExprBlock(string headerFormat, params object[] headerArgs) {
      Contract.Requires(headerFormat != null);
      return NewBigExprBlock(string.Format(headerFormat, headerArgs), null);
    }
        
    public ConcreteSyntaxTree NewBigExprBlock(string header, string/*?*/ footer)
    {
      return NewBlock(header, footer, BraceStyle.Space, BraceStyle.Nothing);
    }

    public ConcreteSyntaxTree NewFile(string filename) {
      var result = new FileSyntax(filename);
      _nodes.Add(result);
      return result.Tree;
    }

    // ----- Collection ------------------------------

    public override string ToString() {
      var sw = new StringWriter();
      var files = new Queue<FileSyntax>();
      Render(sw, 0, new WriterState(), files);
      while (files.Count != 0) {
        var ftw = files.Dequeue();
        sw.WriteLine("#file {0}", ftw.Filename);
        ftw.Render(sw, 0, new WriterState(), files);
      }
      return sw.ToString();
    }

    public void Render(TextWriter writer, int indentation, WriterState writerState,
      Queue<FileSyntax> files)
    {
      foreach (var node in _nodes)
      {
        node.Render(writer, indentation + RelativeIndentLevel * 2, writerState, files);
      }
    }
  }
}