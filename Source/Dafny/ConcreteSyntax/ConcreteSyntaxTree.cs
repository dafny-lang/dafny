using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny
{
  public class ConcreteSyntaxTree : ICanRender {
        
    public ConcreteSyntaxTree(int relativeIndent = 0) {
      RelativeIndentLevel = relativeIndent;
    }

    public readonly int RelativeIndentLevel;

    private readonly IList<ICanRender> _nodes = new List<ICanRender>();

    public IEnumerable<ICanRender> Nodes => _nodes;

    public ConcreteSyntaxTree Fork(int relativeIndent = 0)
    {
      var result = new ConcreteSyntaxTree(relativeIndent);
      _nodes.Add(result);
      return result;
    }

    public T Prepend<T>(T node) 
      where T : ICanRender {
      _nodes.Add(node);
      return node;
    }
    
    public T Append<T>(T node) 
      where T : ICanRender {
      Contract.Requires(node != null);
      _nodes.Add(node);
      return node;
    }

    public ConcreteSyntaxTree Write(object value) {
      Write(value.ToString());
      return this;
    }
        
    public ConcreteSyntaxTree Write(string value) {
      _nodes.Add(new LineSegment(value));
      return this;
    }

    [StringFormatMethod("format")]
    public ConcreteSyntaxTree WriteLine(string format, params object[] args)
    {
      WriteLine(string.Format(format, args));
      return this;
    }

    public ConcreteSyntaxTree WriteLine(string value)
    {
      Write(value);
      WriteLine();
      return this;
    }
        
    public ConcreteSyntaxTree WriteLine()
    {
      _nodes.Add(new NewLine());
      return this;
    }

    [StringFormatMethod("format")]
    public ConcreteSyntaxTree Write(string format, params object[] args)
    {
      Write(string.Format(format, args));
      return this;
    }

    public ConcreteSyntaxTree FormatLine(FormattableString input)
    {
      Format(input);
      return WriteLine();
    }

    public ConcreteSyntaxTree Format(FormattableString input)
    {
      var anchorString = string.Format(input.Format, Enumerable.Range(0, input.ArgumentCount).
        Select(index => $"magicAnchor${index}").ToArray<object>());
      for (int argIndex = 0; argIndex < input.ArgumentCount; argIndex++) {
        var split = anchorString.Split($"magicAnchor${argIndex}");
        anchorString = split.Length > 0 ? split[1] : "";
        Write(split[0]);
        var argument = input.GetArgument(argIndex)!;
        if (argument is string stringArg) {
          Write(stringArg);
        } else {
          Append((ConcreteSyntaxTree)input.GetArgument(argIndex)!);
        }
      }
      if (anchorString != "") {
        Write(anchorString);
      }

      return this;
    }
    
    public ConcreteSyntaxTree Write(char value) {
      Write(new string(value, 1));
      return this;
    }

    // ----- Nested blocks ------------------------------

    public ConcreteSyntaxTree ForkInParens()
    {
      var result = new ConcreteSyntaxTree();
      Write("(");
      Append(result);
      Write(")");
      return result;
    }
        
    public enum BraceStyle { Nothing, Space, Newline }
    
    public ConcreteSyntaxTree NewBlock(string header = "", string footer = "",
      BraceStyle open = BraceStyle.Space,
      BraceStyle close = BraceStyle.Newline) {
      Contract.Requires(header != null);
      Append(Util.Block(out ConcreteSyntaxTree result, header, footer, open, close));
      return result;
    }

    [StringFormatMethod("headerFormat")]
    public ConcreteSyntaxTree NewNamedBlock(string headerFormat, params object[] headerArgs)
    {
      Contract.Requires(headerFormat != null);
      return NewBlock(string.Format(headerFormat, headerArgs), null);
    }

    [StringFormatMethod("headerFormat")]
    public ConcreteSyntaxTree NewExprBlock(string headerFormat, params object[] headerArgs) {
      Contract.Requires(headerFormat != null);
      return NewBigExprBlock(string.Format(headerFormat, headerArgs), null);
    }
        
    public ConcreteSyntaxTree NewBigExprBlock(string header = "", string/*?*/ footer = "")
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