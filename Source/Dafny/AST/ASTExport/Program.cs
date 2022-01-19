using System;
using System.Collections;
using System.Collections.Generic;
using System.Data;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ASTExport;

public static class EnumerableExtensions {
  public static IEnumerable<T> NonNull<T>(this IEnumerable<T?> items) {
    foreach (var item in items) {
      if (item != null) {
        yield return item;
      }
    }
  }
}

abstract class PrettyPrintable {
  protected virtual string ChildIndent => "  ";
  protected virtual string ChildSeparator => Environment.NewLine;

  protected void PpChild(TextWriter wr, string indent, string child) {
    wr.WriteLine($"{indent}{ChildIndent}{child}");
  }

  protected void PpChildren(TextWriter wr, string indent, IEnumerable<PrettyPrintable> children)
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

  private string FmtAttrs(IDictionary<string, string?> attrs) {
    return String.Join(" ", attrs.Select((kv) =>
      String.IsNullOrEmpty(kv.Value) ? $"{{:{kv.Key}}}" : $"{{:{kv.Key} {kv.Value}}}"));
  }

  protected void PpBlockOpen(TextWriter wr, string indent, object? kind, object? name,
    Dictionary<string, string?>? attrs, IEnumerable<Type>? inheritance) {
    var parts = new List<string>();
    parts.Add($"{kind}");
    if (attrs != null) {
      parts.Add(FmtAttrs(attrs));
    }
    parts.Add($"{name}");
    if (inheritance != null) {
      parts.Add($"extends {String.Join(", ", inheritance.Select(t => t.ToString()))}");
    }
    wr.WriteLine($"{indent}{String.Join(" ", parts)} {{");
  }

  protected void PpBlockClose(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}}}");
  }

  public static IEnumerable<PrettyPrintable> Dispatch(SyntaxNode node) {
    return node switch {
      NamespaceDeclarationSyntax s => s.ChildNodes().SelectMany(Dispatch),
      TypeDeclarationSyntax s => new[] { new TypeDecl(s) },
      FieldDeclarationSyntax s => new[] { new Field(s) },
      _ => Enumerable.Empty<PrettyPrintable>()
    };
  }

  public abstract void Pp(TextWriter wr, string indent);
}

class AST : PrettyPrintable {
  private readonly SyntaxTree syntax;

  private AST(SyntaxTree syntax) {
    this.syntax = syntax;
  }

  public static AST FromFile(string fileName) {
    using var reader = new StreamReader(fileName);
    return new AST(CSharpSyntaxTree.ParseText(reader.ReadToEnd()));
  }

  private IEnumerable<PrettyPrintable> Children =>
    syntax.GetCompilationUnitRoot().ChildNodes().SelectMany(Dispatch);

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine("include \"CSharpCompat.dfy\"");
    wr.WriteLine();

    PpBlockOpen(wr, indent, "module", "CSharp",
      new Dictionary<string, string?> {{"extern", "\"SelfHosting.CSharp\""}}, null);

    PpChild(wr, indent, "import opened CSharpGenerics");
    PpChild(wr, indent, "import opened CSharpSystem");
    PpChild(wr, indent, "import opened Boogie");
    PpChild(wr, indent, "import opened Dafny");
    wr.WriteLine();

    PpChildren(wr, indent, Children);

    PpBlockClose(wr, indent);
  }
}

class TypeDecl : PrettyPrintable {
  private readonly TypeDeclarationSyntax syntax;

  protected override string ChildSeparator => "";

  public TypeDecl(TypeDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  private IEnumerable<PrettyPrintable> Children =>
    syntax.ChildNodes().SelectMany(Dispatch);

  public override void Pp(TextWriter wr, string indent) {
    PpBlockOpen(wr, indent, "trait", new Identifier(syntax.Identifier).WithAttrs(),
      new Dictionary<string, string?> {{"compile", "false"}, {"extern", null}},
      syntax.BaseList?.Types.Select(t => new Type(t.Type)));
    PpChildren(wr, indent, Children);
    PpBlockClose(wr, indent);
  }
}

class Enum : PrettyPrintable {
  private readonly EnumDeclarationSyntax syntax;

  public Enum(EnumDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  private IEnumerable<Identifier> Members =>
    syntax.Members.Select(m => new Identifier(m.Identifier));

  public override void Pp(TextWriter wr, string indent) {
    var decl = new Identifier(syntax.Identifier);
    wr.WriteLine($"{indent}datatype {decl.WithAttrs()} =");
    foreach (var m in Members) {
      PpChild(wr, indent, $"| {m.WithAttrs()}");
    }
  }
}

class Field : PrettyPrintable {
  private readonly FieldDeclarationSyntax syntax;

  protected override string ChildSeparator => "";
  protected override string ChildIndent => "";

  public Field(FieldDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  private IEnumerable<Variable> Variables =>
    syntax.Declaration.Variables.Select(v => new Variable(syntax.Declaration.Type, v));

  public override void Pp(TextWriter wr, string indent) {
    PpChildren(wr, indent, Variables);
  }
}

internal class Type {
  private readonly TypeSyntax syntax;

  public Type(TypeSyntax syntax) {
    this.syntax = syntax;
  }

  public override string ToString() {
    if (syntax is ArrayTypeSyntax arr) {
      return $"array<{arr.ElementType.GetText().ToString().Trim()}>";
    }
    return syntax.GetText().ToString().Trim();
  }
}

internal class Identifier {
  private const string EscapePrefix = "CSharp_";
  private static readonly Regex DisallowedNameRe = new Regex("^(type$|_)");

  private readonly SyntaxToken token;

  public Identifier(SyntaxToken token) {
    this.token = token;
  }

  private string Id => token.Text;
  private string EscapedId => Id.StartsWith(EscapePrefix) || DisallowedNameRe.IsMatch(Id) ?
    EscapePrefix + Id : Id;

  public string WithAttrs() {
    string id = Id, eId = EscapedId;
    var attr = id != eId ? $"{{:extern \"{id}\"}} " : "";
    return $"{attr}{eId}";
  }

  public override string ToString() {
    return EscapedId;
  }
}

internal class Variable : PrettyPrintable {
  private readonly Type type;
  private readonly Identifier identifier;

  public Variable(TypeSyntax type, VariableDeclaratorSyntax syntax) {
    this.type = new Type(type);
    this.identifier = new Identifier(syntax.Identifier);
  }

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}var {identifier.WithAttrs()}: {type}");
  }
}

public static class Program {
  public static void Main(string[] args) {
    AST.FromFile(args[0]).Pp(Console.Out, "");
  }
}