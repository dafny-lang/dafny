#nullable enable

using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Build.Locator;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

using CA = Microsoft.CodeAnalysis;

namespace AutoExtern;

abstract class PrettyPrintable {
  protected virtual string ChildIndent => "  ";
  protected virtual string ChildSeparator => Environment.NewLine;

  protected void PpChild(TextWriter wr, string indent, string child) {
    wr.WriteLine($"{indent}{ChildIndent}{child}");
  }

  protected void PpChildren(TextWriter wr, string indent, IEnumerable<PrettyPrintable> children) {
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

  protected void PpBlockOpen(TextWriter wr, string indent, object? kind, Name name,
    IEnumerable<string>? parameters,
    Dictionary<string, string?>? attrs,
    IEnumerable<Type>? inheritance) {
    var parts = new List<string>();
    parts.Add($"{kind}");
    if (attrs is { } nattrs) { // Pattern match instead of != null to placate dotnet-format
      parts.Add(FmtAttrs(nattrs));
    }
    var paramsStr = parameters == null ? "" : $"<{String.Join(", ", parameters)}>";
    parts.Add($"{name.AsDecl(forceExtern: true)}{paramsStr}");
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

internal class SemanticModel {
  private readonly string cSharpRootNS;
  private readonly CA.SemanticModel model;

  public SemanticModel(string cSharpRootNS, CA.SemanticModel model) {
    this.cSharpRootNS = cSharpRootNS;
    this.model = model;
  }

  public ISymbol? GetSymbol(SyntaxNode syntax) {
    return model.GetDeclaredSymbol(syntax);
  }

  public bool IsPublic(SyntaxNode syntax, bool fallback = true) {
    var symbol = GetSymbol(syntax);
    return symbol switch {
      null => fallback,
      { DeclaredAccessibility: Accessibility.Public } => true,
      IPropertySymbol { ExplicitInterfaceImplementations: { IsEmpty: false } } => true,
      _ => false
    };
  }

  private Name GetName(ISymbol? symbol, string fallback) {
    if (symbol == null) {
      return new Name(fallback);
    }

    string WithNs(string ns) => ns == "" ? symbol.Name : $"{ns}.{symbol.Name}";

    // Not ToString() because that includes type parameters (e.g. System.Collections.Generic.List<T>)
    var cs = symbol.ContainingSymbol;
    var ns = symbol is ITypeParameterSymbol || cs is INamespaceSymbol { IsGlobalNamespace: true }
      ? ""
      : cs.ToString() ?? "";

    if (ns.StartsWith(cSharpRootNS)) {
      // For local names return a complete path minus the current module prefix
      var fullName = WithNs(ns.Substring(cSharpRootNS.Length).TrimStart('.'));
      return new Name(fullName, fullName.Replace(".", "__"));
    }

    // For global names use the fully qualified name
    return new Name(WithNs(ns));
  }

  public Name GetName(SyntaxNode node) {
    return node switch {
      EnumMemberDeclarationSyntax s => new Name(s.Identifier),
      EnumDeclarationSyntax s => GetName(GetSymbol(s), $"[UNKNOWN ENUM {s.Identifier.Text}]"),
      TypeDeclarationSyntax s => GetName(GetSymbol(s), $"[UNKNOWN DECL {s.Identifier.Text}]"),
      _ => GetName(model.GetSymbolInfo(node).Symbol, $"[UNKNOWN {node.GetType()} {node}]")
    };
  }
}

internal class AST : PrettyPrintable {
  private readonly SyntaxTree syntax;
  private readonly SemanticModel model;

  public AST(SyntaxTree syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  public static IEnumerable<AST> FromFiles(string projectPath, IEnumerable<string> sourceFiles, string cSharpRootNS) {
    // https://github.com/dotnet/roslyn/issues/44586
    MSBuildLocator.RegisterDefaults();
    var workspace = Microsoft.CodeAnalysis.MSBuild.MSBuildWorkspace.Create();
    workspace.LoadMetadataForReferencedProjects = true;

    var project = workspace.OpenProjectAsync(projectPath).Result;

    //var errors = workspace.Diagnostics.Select()
    if (!workspace.Diagnostics.IsEmpty) {
      foreach (var diagnostic in workspace.Diagnostics) {
        Console.Error.WriteLine("Error in project: {0}", diagnostic.Message);
      }
      throw new Exception("Unexpected errors while building project");
    }

    var compilation = project.GetCompilationAsync().Result!;
    return sourceFiles.Select(filePath => {
      var fullPath = Path.GetFullPath(filePath);
      var syntax = compilation.SyntaxTrees.First(st => Path.GetFullPath(st.FilePath) == fullPath);
      var model = compilation.GetSemanticModel(syntax);
      return new AST(syntax, new SemanticModel(cSharpRootNS, model));
    });
  }

  private CompilationUnitSyntax Root => syntax.GetCompilationUnitRoot();

  private IEnumerable<PrettyPrintable> Decls =>
    Enumerable.Empty<PrettyPrintable>()
      .Concat(Root.DescendantNodes().OfType<EnumDeclarationSyntax>().Select(s => new Enum(s, model)))
      .Concat(Root.DescendantNodes().OfType<TypeDeclarationSyntax>().Select(s => new TypeDecl(s, model)));

  public override void Pp(TextWriter wr, string indent) {
    PpChildren(wr, indent, Decls);
  }
}

internal class TypeDecl : PrettyPrintable {
  private readonly TypeDeclarationSyntax syntax;
  private readonly SemanticModel model;

  protected override string ChildSeparator => "";

  public TypeDecl(TypeDeclarationSyntax syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  public Name IntfName => Name.OfSyntax(syntax, model);

  private bool IsInterface => syntax.Keyword.ToString() == "interface";

  private IEnumerable<PrettyPrintable> Fields =>
    syntax.ChildNodes().OfType<FieldDeclarationSyntax>() // Filtering for `public` fields is done later
      .Select(s => new Field(s, model));

  private IEnumerable<PrettyPrintable> Properties =>
    syntax.ChildNodes().OfType<PropertyDeclarationSyntax>().Where(v => model.IsPublic(v))
      .Select(s => new Property(s, model, IsInterface ? this : null));

  public override void Pp(TextWriter wr, string indent) {
    PpBlockOpen(wr, indent, "trait", IntfName,
      syntax.TypeParameterList?.Parameters.Select(s => new Name(s.Identifier).DafnyId),
      new Dictionary<string, string?> { { "compile", "false" } },
      syntax.BaseList?.Types.Select(t => new Type(t.Type, model)));
    PpChildren(wr, indent, Fields);
    PpChildren(wr, indent, Properties);
    PpBlockClose(wr, indent);
  }
}

internal class Enum : PrettyPrintable {
  private readonly EnumDeclarationSyntax syntax;
  private readonly SemanticModel model;

  protected override string ChildSeparator => "";

  public Enum(EnumDeclarationSyntax syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  private IEnumerable<EnumMember> Members =>
    syntax.Members.Select(m => new EnumMember(m, model));

  public override void Pp(TextWriter wr, string indent) {
    var nm = Name.OfSyntax(syntax, model);
    PpBlockOpen(wr, indent, "class", nm, null, null, null);
    PpChildren(wr, indent, Members);
    PpChild(wr, indent, $"function method {{:extern}} Equals(other: {nm.DafnyId}): bool");
    PpBlockClose(wr, indent);
  }
}

internal class EnumMember : PrettyPrintable {
  private readonly EnumMemberDeclarationSyntax syntax;
  private readonly SemanticModel model;

  public EnumMember(EnumMemberDeclarationSyntax syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  public override void Pp(TextWriter wr, string indent) {
    var decl = Name.OfSyntax(syntax, model).AsDecl(forceExtern: true);
    var type = Name.OfSyntax(this.syntax.Parent!, model).DafnyId;
    wr.WriteLine($"{indent}static const {decl}: {type}");
  }
}

internal class Field : PrettyPrintable {
  private readonly FieldDeclarationSyntax syntax;
  private readonly SemanticModel model;

  protected override string ChildSeparator => "";
  protected override string ChildIndent => "";

  public Field(FieldDeclarationSyntax syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  private IEnumerable<Variable> Variables =>
    syntax.Declaration.Variables.Where(v => model.IsPublic(v))
      .Select(v => new Variable(syntax.Declaration.Type, v, model));

  public override void Pp(TextWriter wr, string indent) {
    PpChildren(wr, indent, Variables);
  }
}

internal class Property : PrettyPrintable {
  private readonly PropertyDeclarationSyntax syntax;
  private readonly SemanticModel model;
  private readonly Type type;
  private readonly TypeDecl? parentInterface;

  protected override string ChildSeparator => "";
  protected override string ChildIndent => "";

  public Property(PropertyDeclarationSyntax syntax, SemanticModel model, TypeDecl? parentInterface) {
    this.syntax = syntax;
    this.model = model;
    this.parentInterface = parentInterface;
    this.type = new Type(syntax.Type, model);
  }

  private bool ExistsInAncestor(ITypeSymbol typeSymbol) {
    var baseType = typeSymbol?.BaseType;
    return baseType != null &&
      (baseType.GetMembers(syntax.Identifier.Text).Length > 0 ||
       ExistsInAncestor(baseType));
  }

  public override void Pp(TextWriter wr, string indent) {
    var name = new Name(syntax.Identifier);
    var symbol = model.GetSymbol(syntax);
    var comment = " // property";
    var prefix = "";

    if (parentInterface != null) {
      name = new Name(name.CSharpID, $"{parentInterface.IntfName.DafnyId}_{name.DafnyId}");
      comment = " // interface property";
    } else if (symbol is not null && ExistsInAncestor(symbol.ContainingType)) {
      prefix = "// ";
      comment = " // property that exists in ancestor";
    } else if (syntax.ExplicitInterfaceSpecifier is not null) {
      prefix = "// ";
      comment = " // explicit interface property";
    }

    wr.WriteLine($"{indent}{prefix}var {name.AsDecl()}: {type}{comment}");
  }
}

internal class Type {
  private readonly TypeSyntax syntax;
  private readonly SemanticModel model;

  public Type(TypeSyntax syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  private string GenericNameToString(GenericNameSyntax s) {
    var name = s.Identifier.Text switch {
      "Tuple" => $"System.Tuple{s.TypeArgumentList.Arguments.Count}",
      _ => Name.OfSyntax(s, model).DafnyId
    };
    var typeArgs = String.Join(", ", s.TypeArgumentList.Arguments.Select(t => new Type(t, model)));
    return @$"{name}<{typeArgs}>";
  }

  public override string ToString() {
    return syntax switch {
      PredefinedTypeSyntax { Keyword: { Text: var text } } => text switch {
        "int" => "System.int32", // Native int32 (a value type), not System.Int32 (an object)
        "string" => "System.String",
        "bool" => "bool", // Native bool (a value type), not System.Boolean (an object)
        _ => text
      },
      ArrayTypeSyntax s =>
        $"array<{new Type(s.ElementType, model)}>",
      GenericNameSyntax s =>
        GenericNameToString(s),
      SimpleNameSyntax { Identifier: { Text: "BigInteger" } } =>
        "int",
      _ =>
        Name.OfSyntax(syntax, model).DafnyId, // TODO
    };
  }
}

internal class Variable : PrettyPrintable {
  private readonly Type type;
  private readonly SyntaxToken identifier;

  public Variable(TypeSyntax type, VariableDeclaratorSyntax syntax, SemanticModel model) {
    this.type = new Type(type, model);
    this.identifier = syntax.Identifier;
  }

  public override void Pp(TextWriter wr, string indent) {
    wr.WriteLine($"{indent}var {new Name(identifier).AsDecl()}: {type}");
  }
}

internal class Name {
  private const string EscapePrefix = "CSharp_";

  private static readonly List<string> DisallowedNameWords = new List<string>
    {"type", "ORDINAL", "Keys", "Values", "Items", "IsLimit", "IsSucc", "Offset", "IsNat"};
  private static readonly Regex DisallowedNameRe =
    new Regex($"^(_|({String.Join("|", DisallowedNameWords)})$)");

  public readonly string DafnyId;
  public readonly string CSharpID;

  public Name(string cSharpID, string dafnyID) {
    this.CSharpID = cSharpID;
    this.DafnyId = dafnyID.StartsWith(EscapePrefix) || DisallowedNameRe.IsMatch(dafnyID) ?
      EscapePrefix + dafnyID : dafnyID;
  }

  public Name(string cSharpId) : this(cSharpId, cSharpId) {
  }

  public Name(SyntaxToken token) : this(token.Text) {
  }

  public static Name OfSyntax(SyntaxNode node, SemanticModel model) {
    return model.GetName(node);
  }

  public string AsDecl(bool forceExtern = false) {
    var attr = CSharpID != DafnyId ? $"{{:extern \"{CSharpID}\"}} " : forceExtern ? "{:extern} " : "";
    return $"{attr}{DafnyId}";
  }
}

public static class Program {
  private const string Placeholder = "{{{AutoExtern}}}";

  private static void Fail(string msg) {
    Console.Error.WriteLine("Error: {0}", msg);
    Environment.Exit(1);
  }

  public static string ReadTemplate(string templatePath) {
    var template = File.ReadAllText(templatePath, Encoding.UTF8);
    if (!template.Contains(Placeholder)) {
      Fail($"Template file {templatePath} does not contain {Placeholder} string.");
    }
    return template;
  }

  public static string GenerateDafnyCode(string projectPath, IList<string> sourceFiles, string cSharpRootNS) {
    var wr = new StringWriter();
    var asts = AST.FromFiles(projectPath, sourceFiles, cSharpRootNS).ToList();
    var last = asts.Last();
    foreach (var ast in asts) {
      ast.Pp(wr, "");
      if (ast != last) {
        wr.WriteLine();
      }
    }
    return wr.ToString();
  }

  public static void CopyCSharpModel(string destPath) {
    if (destPath != "") {
      var exe = System.Reflection.Assembly.GetExecutingAssembly().Location;
      var sourcePath = Path.Join(Path.GetDirectoryName(exe), "CSharpModel.dfy");
      File.Copy(sourcePath, destPath, true);
    }
  }

  public static void Main(string[] args) {
    if (args.Length < 6) {
      Fail("Usage: AutoExtern {project.csproj} {Root.Namespace} {TemplateFile.dfy} {CSharpModel.dfy} {Output.dfy} {file.cs}*");
    }

    var (projectPath, cSharpRootNS, templatePath, modelPath, outputPath) =
      (args[0], args[1], args[2], args[3], args[4]);
    var sourceFiles = args.Skip(5).ToList();

    var dafnyCode = GenerateDafnyCode(projectPath, sourceFiles, cSharpRootNS);
    var template = ReadTemplate(templatePath);
    File.WriteAllText(outputPath, template.Replace(Placeholder, dafnyCode), Encoding.UTF8);

    CopyCSharpModel(modelPath);
  }
}
