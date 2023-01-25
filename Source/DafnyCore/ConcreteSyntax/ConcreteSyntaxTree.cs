using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny {
  public enum BlockStyle {
    Nothing,
    Space,
    Newline,
    Brace,
    SpaceBrace,
    NewlineBrace
  }

  public class ConcreteSyntaxTree : ICanRender, IList<ICanRender> {
    public ConcreteSyntaxTree(int relativeIndent = 0) {
      RelativeIndentLevel = relativeIndent;
    }

    public readonly int RelativeIndentLevel;

    private readonly IList<ICanRender> _nodes = new List<ICanRender>();

    public IEnumerable<ICanRender> Nodes => _nodes;

    public ConcreteSyntaxTree Fork(int relativeIndent = 0) {
      var result = new ConcreteSyntaxTree(relativeIndent);
      _nodes.Add(result);
      return result;
    }

    void ICollection<ICanRender>.Add(ICanRender item) {
      _nodes.Add(item);
    }

    public void Clear() {
      while (_nodes.Any()) {
        _nodes.RemoveAt(0);
      }
    }

    bool ICollection<ICanRender>.Contains(ICanRender item) {
      return _nodes.Contains(item);
    }

    void ICollection<ICanRender>.CopyTo(ICanRender[] array, int arrayIndex) {
      _nodes.CopyTo(array, arrayIndex);
    }

    bool ICollection<ICanRender>.Remove(ICanRender item) {
      return _nodes.Remove(item);
    }

    int ICollection<ICanRender>.Count => _nodes.Count;

    bool ICollection<ICanRender>.IsReadOnly => _nodes.IsReadOnly;

    public T Prepend<T>(T node)
      where T : ICanRender {
      _nodes.Insert(0, node);
      return node;
    }

    public T Append<T>(T node)
      where T : ICanRender {
      Contract.Requires(node != null);
      _nodes.Add(node);
      return node;
    }

    public ConcreteSyntaxTree Write(string value) {
      _nodes.Add(new LineSegment(value));
      return this;
    }

    [StringFormatMethod("format")]
    public ConcreteSyntaxTree WriteLine(string format, params object[] args) {
      WriteLine(string.Format(format, args));
      return this;
    }

    public ConcreteSyntaxTree WriteLine(string value) {
      Write(value);
      WriteLine();
      return this;
    }

    public ConcreteSyntaxTree WriteLine() {
      _nodes.Add(new NewLine());
      return this;
    }

    [StringFormatMethod("format")]
    public ConcreteSyntaxTree Write(string format, params object[] args) {
      Write(string.Format(format, args));
      return this;
    }

    public ConcreteSyntaxTree FormatLine(FormattableString input) {
      Format(input);
      return WriteLine();
    }

    static string anchorUUID = "20e34a49-f40b-4547-ba7a-3a1955826af2";

    public ConcreteSyntaxTree Format(FormattableString input) {
      var anchorValues = new List<ConcreteSyntaxTree>();
      // Because template strings are difficult to process, we use the existing string.Format to do the processing
      // and we insert anchors to identify where the ConcreteSyntaxTree values are.
      // Template string processing logic can be found here: https://github.com/dotnet/runtime/blob/ae5ee8f02d6fc99469e1f194be45b5f649c2da1a/src/libraries/System.Private.CoreLib/src/System/Text/ValueStringBuilder.AppendFormat.cs#L60
      var formatArguments = Enumerable.Range(0, input.ArgumentCount).
        Select(index => {
          object argument = input.GetArgument(index)!;
          if (argument is ConcreteSyntaxTree treeArg) {
            anchorValues.Add(treeArg);
            return $"{anchorUUID}{anchorValues.Count - 1}";
          }

          return argument;
        }).ToArray();

      var anchorString = string.Format(input.Format, formatArguments);
      for (int argIndex = 0; argIndex < anchorValues.Count; argIndex++) {
        var split = anchorString.Split($"{anchorUUID}{argIndex}");
        anchorString = split.Length > 1 ? split[1] : "";
        Write(split[0]);
        Append(anchorValues[argIndex]);
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

    public ConcreteSyntaxTree ForkInParens() {
      var result = new ConcreteSyntaxTree();
      Write("(");
      Append(result);
      Write(")");
      return result;
    }

    public ConcreteSyntaxTree NewBlock(string header = "", string footer = "",
      BlockStyle open = BlockStyle.SpaceBrace,
      BlockStyle close = BlockStyle.NewlineBrace) {
      Contract.Requires(header != null);
      Append(ConcreteSyntaxTreeUtils.Block(out ConcreteSyntaxTree result, header: header, footer: footer, open: open,
        close: close));
      return result;
    }

    [StringFormatMethod("headerFormat")]
    public ConcreteSyntaxTree NewNamedBlock(string headerFormat, params object[] headerArgs) {
      Contract.Requires(headerFormat != null);
      return NewBlock(string.Format(headerFormat, headerArgs), null);
    }

    [StringFormatMethod("headerFormat")]
    public ConcreteSyntaxTree NewExprBlock(string headerFormat, params object[] headerArgs) {
      Contract.Requires(headerFormat != null);
      return NewBigExprBlock(string.Format(headerFormat, headerArgs), null);
    }

    public ConcreteSyntaxTree NewBigExprBlock(string header = "", string /*?*/ footer = "") {
      return NewBlock(header, footer, BlockStyle.SpaceBrace, BlockStyle.Brace);
    }

    public ConcreteSyntaxTree NewFile(string filename) {
      var result = new FileSyntax(filename);
      _nodes.Add(result);
      return result.Tree;
    }

    // ----- Collection ------------------------------

    IEnumerator<ICanRender> IEnumerable<ICanRender>.GetEnumerator() {
      return _nodes.GetEnumerator();
    }

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

    IEnumerator IEnumerable.GetEnumerator() {
      return ((IEnumerable) _nodes).GetEnumerator();
    }

    public void Render(TextWriter writer, int indentation, WriterState writerState, Queue<FileSyntax> files, int indentSize = 2) {
      foreach (var node in _nodes) {
        node.Render(writer, indentation + RelativeIndentLevel * indentSize, writerState, files, indentSize);
      }
    }

    int IList<ICanRender>.IndexOf(ICanRender item) {
      return _nodes.IndexOf(item);
    }

    void IList<ICanRender>.Insert(int index, ICanRender item) {
      _nodes.Insert(index, item);
    }

    void IList<ICanRender>.RemoveAt(int index) {
      _nodes.RemoveAt(index);
    }

    ICanRender IList<ICanRender>.this[int index] {
      get => _nodes[index];
      set => _nodes[index] = value;
    }
  }
}