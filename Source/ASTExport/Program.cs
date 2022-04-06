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
    IEnumerable<string>? parameters,
    Dictionary<string, string?>? attrs,
    IEnumerable<Type>? inheritance)
  {
    var parts = new List<string>();
    parts.Add($"{kind}");
    if (attrs != null) {
      parts.Add(FmtAttrs(attrs));
    }
    var paramsStr = parameters == null ? "" : $"<{String.Join(", ", parameters)}>";
    parts.Add($"{name}{paramsStr}");
    if (inheritance != null) {
      parts.Add($"extends {String.Join(", ", inheritance.Select(t => t.ToString()))}");
    }
    wr.WriteLine($"{indent}{String.Join(" ", parts)} {{");
  }

  protected void PpBlockClose(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}}}");
  }

  public abstract void Pp(TextWriter wr, string indent);
}

class AST : PrettyPrintable {
  private readonly string rootName;
  private readonly SyntaxTree syntax;

  private AST(string rootName, SyntaxTree syntax) {
    this.syntax = syntax;
    this.rootName = rootName;
  }

  public static AST FromFile(string fileName, string rootName) {
    using var reader = new StreamReader(fileName);
    return new AST(rootName, CSharpSyntaxTree.ParseText(reader.ReadToEnd()));
  }

  private CompilationUnitSyntax Root => syntax.GetCompilationUnitRoot();

  private IEnumerable<PrettyPrintable> Decls =>
    Enumerable.Empty<PrettyPrintable>()
      .Concat(Root.DescendantNodes().OfType<EnumDeclarationSyntax>().Select(s => new Enum(s)))
      .Concat(Root.DescendantNodes().OfType<TypeDeclarationSyntax>().Select(s => new TypeDecl(s)));

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine("include \"CSharpCompat.dfy\"");
    wr.WriteLine();

    PpBlockOpen(wr, indent, "module", rootName,
      null, new Dictionary<string, string?> {{"extern", $"\"{rootName}\""}}, null);

    PpChild(wr, indent, "import opened CSharpGenerics");
    PpChild(wr, indent, "import opened CSharpSystem");
    PpChild(wr, indent, "import opened Boogie");
    PpChild(wr, indent, "import opened Dafny");
    wr.WriteLine();

    PpChildren(wr, indent, Decls);

    PpBlockClose(wr, indent);
  }
}

class TypeDecl : PrettyPrintable {
  private readonly TypeDeclarationSyntax syntax;

  protected override string ChildSeparator => "";

  public TypeDecl(TypeDeclarationSyntax syntax) {
    this.syntax = syntax;
  }

  private IEnumerable<PrettyPrintable> Fields =>
    syntax.ChildNodes().OfType<FieldDeclarationSyntax>().Select(s => new Field(s));

  public override void Pp(TextWriter wr, string indent) {
    PpBlockOpen(wr, indent, "trait", new Identifier(syntax.Identifier),
      syntax.TypeParameterList?.Parameters.Select(s => new Identifier(s.Identifier).EscapedId),
      new Dictionary<string, string?> {{"compile", "false"}, {"extern", null}},
      syntax.BaseList?.Types.Select(t => new Type(t.Type)));
    PpChildren(wr, indent, Fields);
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
    wr.WriteLine($"{indent}datatype {decl} =");
    foreach (var m in Members) {
      PpChild(wr, indent, $"| {m}");
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

  private static string GenericNameToString(GenericNameSyntax s) {
    var name = s.Identifier.Text switch {
      "Tuple" => $"Tuple{s.TypeArgumentList.Arguments.Count}",
      _ => new Identifier(s.Identifier).EscapedId
    };
    var typeArgs = String.Join(", ", s.TypeArgumentList.Arguments.Select(t => new Type(t)));
    return @$"{name}<{typeArgs}>";
  }

  public override string ToString() {
    return syntax switch {
      ArrayTypeSyntax s =>
        $"array<{new Type(s.ElementType)}>",
      GenericNameSyntax s =>
        GenericNameToString(s),
      SimpleNameSyntax s =>
        s.Identifier.Text switch {
          "BigInteger" => "int",
          _ => new Identifier(s.Identifier).ToString(),
        },
      QualifiedNameSyntax s when s.Left.ToString() != "Boogie" =>
        // Drop qualifications since we flatten the nested structure
        new Identifier(s.Right.Identifier).ToString(),
      _ =>
        syntax.GetText().ToString().Trim()
    };
  }
}

internal class Identifier {
  private const string EscapePrefix = "CSharp_";
  private static readonly Regex DisallowedNameRe = new Regex("^(type$|ORDINAL$|_)");

  private readonly SyntaxToken token;

  public Identifier(SyntaxToken token) {
    this.token = token;
  }

  private string Id => token.Text;

  public string EscapedId => Id.StartsWith(EscapePrefix) || DisallowedNameRe.IsMatch(Id) ?
    EscapePrefix + Id : Id;

  public override string ToString() {
    string id = Id, eId = EscapedId;
    var attr = id != eId ? $"{{:extern \"{id}\"}} " : "";
    return $"{attr}{eId}";
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
    wr.WriteLine($"{indent}var {identifier}: {type}");
  }
}

public static class Program {
  public static void Main(string[] args) {
    AST.FromFile(args[0], args[1]).Pp(Console.Out, "");
  }
}