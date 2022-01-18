using System;
using System.Collections;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ASTExport;

abstract class PrettyPrintable {
  protected virtual string ChildIndent => "  ";
  protected virtual string ChildSeparator => Environment.NewLine;

  protected void PpChild(TextWriter wr, string indent, string child) {
    wr.WriteLine($"{indent}{ChildIndent}{child}");
  }

  protected void PpChildren<T>(TextWriter wr, string indent, IEnumerable<T> children)
    where T : PrettyPrintable
  {
    indent += ChildIndent;
    var childrenList = children.ToList();
    for (var idx = 0; idx < childrenList.Count; idx++) {
      childrenList[idx].Pp(wr, indent);
      if (idx < childrenList.Count - 1) {
        wr.Write(ChildSeparator);
      }
    }
  }

  public string FmtAttrs(IDictionary<string, string?> attrs) {
    return String.Join(" ", attrs.Select((kv) =>
      String.IsNullOrEmpty(kv.Value) ? $"{{:{kv.Key}}}" : $"{{:{kv.Key} {kv.Value}}}"));
  }

  protected void PpBlockOpen(TextWriter wr, string indent, string kind, string name,
    Dictionary<string, string?>? attrs, IEnumerable<string>? inheritance) {
    var parts = new List<string>() {kind};
    if (attrs != null) {
      parts.Add(FmtAttrs(attrs));
    }
    parts.Add(name);
    if (inheritance != null) {
      parts.Add($"extends {String.Join(", ", inheritance)}");
    }
    wr.WriteLine($"{indent}{String.Join(" ", parts)} {{");
  }

  protected void PpBlockClose(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}}}");
  }

  public abstract void Pp(TextWriter wr, string indent);
}

class AST : PrettyPrintable {
  private readonly SyntaxTree syntax;

  private AST(SyntaxTree syntax) {
    this.syntax = syntax;
  }

  public static AST FromFile(string fname) {
    using var reader = new StreamReader(fname);
    return new AST(CSharpSyntaxTree.ParseText(reader.ReadToEnd()));
  }

  public IEnumerable<Class> Classes =>
    syntax.GetCompilationUnitRoot().DescendantNodes().OfType<ClassDeclarationSyntax>()
      .Select(c => new Class(c));

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine("include \"CSharpCompat.dfy\"");
    wr.WriteLine();
    PpBlockOpen(wr, indent, "module", "CSharp",
      new Dictionary<string, string?> {{"extern", "\"SelfHosting.CSharp\""}}, null);
    PpChild(wr, indent, "import opened CSharpGenerics");
    wr.WriteLine();
    PpChildren(wr, indent, Classes);
    PpBlockClose(wr, indent);
  }
}

class Class : PrettyPrintable {
  private readonly ClassDeclarationSyntax syntax;

  public Class(ClassDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  public IEnumerable<Field> Fields =>
    syntax.DescendantNodes().OfType<FieldDeclarationSyntax>().Select(f => new Field(f));

  public override void Pp(TextWriter wr, string indent) {
    PpBlockOpen(wr, indent, "trait", syntax.Identifier.Text,
      new Dictionary<string, string?> {{"compile", "false"}, {"extern", null}},
      syntax.BaseList?.Types.Select(t => t.Type.GetText().ToString().Trim()));
    PpChildren(wr, indent, Fields);
    PpBlockClose(wr, indent);
  }
}

class Field : PrettyPrintable {
  private readonly FieldDeclarationSyntax syntax;

  protected override string ChildSeparator => "";
  protected override string ChildIndent => "";

  public Field(FieldDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  public IEnumerable<Variable> Variables =>
    syntax.Declaration.Variables.Select(v => new Variable(syntax.Declaration.Type, v));

  public override void Pp(TextWriter wr, string indent) {
    PpChildren(wr, indent, Variables);
  }
}

internal class Variable : PrettyPrintable {
  private readonly TypeSyntax type;
  private readonly VariableDeclaratorSyntax syntax;

  public Variable(TypeSyntax type, VariableDeclaratorSyntax syntax) {
    this.type = type;
    this.syntax = syntax;
  }

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}var {syntax.Identifier.Text}: {type.GetText().ToString().Trim()}");
  }
}

public static class Program {
  public static void Main(string[] args) {
    AST.FromFile(args[0]).Pp(Console.Out, "");
  }
}