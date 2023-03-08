#nullable enable

using System.Text;
using System.Text.RegularExpressions;
using System.CommandLine;
using System.CommandLine.Parsing;
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

public interface INameRewriter {
  string Rewrite(string name);
}

internal class SemanticModel {
  private readonly string rootModule;
  private readonly INameRewriter nameRewriter;
  private readonly IList<string> skippedInterfaces;
  private readonly CA.SemanticModel model;

  public SemanticModel(string rootModule, INameRewriter nameRewriter, IList<string> skippedInterfaces, CA.SemanticModel model) {
    this.rootModule = rootModule;
    this.nameRewriter = nameRewriter;
    this.skippedInterfaces = skippedInterfaces;
    this.model = model;
  }

  public ISymbol? GetSymbol(SyntaxNode syntax) {
    return model.GetDeclaredSymbol(syntax);
  }

  public ISymbol? GetSymbolInfo(SyntaxNode syntax) {
    return model.GetSymbolInfo(syntax).Symbol;
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

    // Not ToString() because that includes type parameters (e.g. System.Collections.Generic.List<T>)
    var cs = symbol.ContainingSymbol;
    var ns = symbol is ITypeParameterSymbol || cs is INamespaceSymbol { IsGlobalNamespace: true }
      ? "" : cs.ToString() ?? "";

    var isLocalName = ns.StartsWith(rootModule);
    var cSharpName = nameRewriter.Rewrite(ns == "" ? symbol.Name : $"{ns}.{symbol.Name}");
    var dafnyName = isLocalName ? cSharpName.Replace(".", "__") : cSharpName;
    return new Name(cSharpName, dafnyName);
  }

  public Name GetName(SyntaxNode node) {
    return node switch {
      EnumMemberDeclarationSyntax s => new Name(s.Identifier),
      EnumDeclarationSyntax s => GetName(GetSymbol(s), $"[UNKNOWN ENUM {s.Identifier.Text}]"),
      TypeDeclarationSyntax s => GetName(GetSymbol(s), $"[UNKNOWN DECL {s.Identifier.Text}]"),
      _ => GetName(GetSymbolInfo(node), $"[UNKNOWN {node.GetType()} {node}]")
    };
  }

  public bool IsSkippedInterface(ISymbol symbol) {
    var fullName = symbol.ContainingNamespace + "." + symbol.Name;
    return skippedInterfaces.Contains(fullName);
  }
}

internal class CSharpFile : PrettyPrintable {
  private readonly SyntaxTree syntax;
  private readonly SemanticModel model;

  private CSharpFile(SyntaxTree syntax, SemanticModel model) {
    this.syntax = syntax;
    this.model = model;
  }

  public static IEnumerable<CSharpFile> FromFiles(
    string projectPath, IEnumerable<string> sourceFiles,
    string rootModule, INameRewriter nameRewriter, IList<string> skippedInterfaces) {
    // https://github.com/dotnet/roslyn/issues/44586
    MSBuildLocator.RegisterDefaults();
    var workspace = Microsoft.CodeAnalysis.MSBuild.MSBuildWorkspace.Create();
    workspace.LoadMetadataForReferencedProjects = true;

    var project = workspace.OpenProjectAsync(projectPath).Result;

    if (!workspace.Diagnostics.IsEmpty) {
      foreach (var diagnostic in workspace.Diagnostics) {
        Console.Error.WriteLine("Error in project: {0}", diagnostic.Message);
      }
      throw new Exception("Unexpected errors while building project");
    }

    var compilation = project.GetCompilationAsync().Result!;
    var syntaxTrees = compilation.SyntaxTrees.ToDictionary(
      st => Path.GetFullPath(st.FilePath),
      st => st);

    return sourceFiles.Select(filePath => {
      var fullPath = Path.GetFullPath(filePath);
      if (!syntaxTrees.TryGetValue(fullPath, out var syntax)) {
        Console.WriteLine($"Error: No syntax tree found in project '{projectPath}' for file '{fullPath}'.");
        Console.WriteLine($"Known paths in project ({syntaxTrees.Count} total):");
        foreach (var key in syntaxTrees) {
          Console.WriteLine($"  {key}");
        }
        throw new Exception("Unexpected errors while building project");
      }
      var model = compilation.GetSemanticModel(syntax);
      return new CSharpFile(syntax, new SemanticModel(rootModule, nameRewriter, skippedInterfaces, model));
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

  private bool IsSkippedBaseType(BaseTypeSyntax bt) {
    return model.GetSymbolInfo(bt.Type) is { } baseType && model.IsSkippedInterface(baseType);
  }

  private IEnumerable<Type> BaseTypes =>
    syntax.BaseList?.Types
      .Where(bt => !IsSkippedBaseType(bt))
      .Select(bt => new Type(bt.Type, model))
    ?? Enumerable.Empty<Type>();

  public override void Pp(TextWriter wr, string indent) {
    var baseTypes = BaseTypes.ToList();
    PpBlockOpen(wr, indent, "trait", IntfName,
      syntax.TypeParameterList?.Parameters.Select(s => new Name(s.Identifier).DafnyId),
      new Dictionary<string, string?> { { "compile", "false" } },
      baseTypes.Any() ? baseTypes : null);
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
    PpChild(wr, indent, $"function {{:extern}} Equals(other: {nm.DafnyId}): bool");
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

  private bool ExistsInAncestor(ITypeSymbol? typeSymbol) {
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
      name = new Name(name.CSharpId, $"{parentInterface.IntfName.DafnyId}_{name.DafnyId}");
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
  public readonly string CSharpId;

  public Name(string cSharpId, string dafnyId) {
    this.CSharpId = cSharpId;
    this.DafnyId = dafnyId.StartsWith(EscapePrefix) || DisallowedNameRe.IsMatch(dafnyId) ?
      EscapePrefix + dafnyId : dafnyId;
  }

  public Name(string cSharpId) : this(cSharpId, cSharpId) {
  }

  public Name(SyntaxToken token) : this(token.Text) {
  }

  public static Name OfSyntax(SyntaxNode node, SemanticModel model) {
    return model.GetName(node);
  }

  public string AsDecl(bool forceExtern = false) {
    var attr = CSharpId != DafnyId ? $"{{:extern \"{CSharpId}\"}} " : forceExtern ? "{:extern} " : "";
    return $"{attr}{DafnyId}";
  }
}

public static class Program {
  private const string Placeholder = "{{{AutoExtern}}}";

  private static void Fail(string msg) {
    Console.Error.WriteLine("Error: {0}", msg);
    Environment.Exit(1);
  }

  private static string ReadTemplate(string templatePath) {
    var template = File.ReadAllText(templatePath, Encoding.UTF8);
    if (!template.Contains(Placeholder)) {
      Fail($"Template file {templatePath} does not contain {Placeholder} string.");
    }
    return template;
  }

  private static string GenerateDafnyCode(
    string projectPath, IList<string> sourceFiles,
    string rootModule, INameRewriter nameRewriter, IList<string> skippedInterfaces) {
    var wr = new StringWriter();
    var asts = CSharpFile.FromFiles(projectPath, sourceFiles, rootModule, nameRewriter, skippedInterfaces).ToList();
    var last = asts.Last();
    foreach (var ast in asts) {
      ast.Pp(wr, "");
      if (ast != last) {
        wr.WriteLine();
      }
    }
    return wr.ToString();
  }

  private static void CopyCSharpModel(string destPath) {
    if (destPath != "") {
      var exe = System.Reflection.Assembly.GetExecutingAssembly().Location;
      var sourcePath = Path.Join(Path.GetDirectoryName(exe), "CSharpModel.dfy");
      File.Copy(sourcePath, destPath, true);
    }
  }

  record SimpleNameRewriter(List<(string, string)> Rewrites) : INameRewriter {
    public string Rewrite(string name) {
      foreach (var (src, dst) in Rewrites) {
        if (name.StartsWith(src)) {
          name = dst + name.Substring(src.Length);
          break;
        }
      }
      return name;
    }
  }

  public static int Main(string[] args) {
    var rootCommand = new RootCommand("Generate Dafny models of C# types.");

    var projectPathArgument = new Argument<string>(
      name: "project",
      description: "The C# project file that owns the files to translate to Dafny."
    );
    rootCommand.AddArgument(projectPathArgument);

    var rootModuleArgument = new Argument<string>(
      name: "root-module",
      description: "The name of the Dafny module that will contain this code."
    );
    rootCommand.AddArgument(rootModuleArgument);

    var templatePathArgument = new Argument<string>(
      name: "template",
      description: "The template file to copy translated definitions into.  " +
                   $"This file must contain the string '{Placeholder}'.");
    rootCommand.AddArgument(templatePathArgument);

    var modelPathArgument = new Argument<string>(
      name: "model-output",
      description: "Where to write CSharpModel.dfy, a file containing shared C# definitions.");
    rootCommand.AddArgument(modelPathArgument);

    var outputPathArgument = new Argument<string>(
      name: "output",
      description: "Where to write the generated Dafny model.");
    rootCommand.AddArgument(outputPathArgument);

    var sourceFilesArgument = new Argument<List<string>>(
      name: "input...",
      description: "C# files to translate.") {
      Arity = ArgumentArity.OneOrMore
    };
    rootCommand.AddArgument(sourceFilesArgument);

    var nameRewritesOption = new Option<List<(string, string)>>(
      name: "--rewrite",
      description: "A name-rewriting specification, e.g. `--rewrite X.Y.:A.B.`.",
      parseArgument: ParseRewrites) {
      ArgumentHelpName = "before:after",
      Arity = ArgumentArity.ExactlyOne,
      AllowMultipleArgumentsPerToken = false
    };
    rootCommand.AddOption(nameRewritesOption);

    var skipInterfaceOption = new Option<List<string>>(
      name: "--skip-interface",
      description: "An interface to ommit from `extends` lists, e.g. `--skip-interface Microsoft.Dafny.ICloneable`.") {
      ArgumentHelpName = "interfaceName",
      Arity = ArgumentArity.ZeroOrMore,
      AllowMultipleArgumentsPerToken = false
    };
    rootCommand.AddOption(skipInterfaceOption);

    Action<string, string, List<(string, string)>, List<string>, string, string, string, List<string>>
      main = ParsedMain;
    rootCommand.SetHandler(main,
      projectPathArgument, rootModuleArgument, nameRewritesOption, skipInterfaceOption,
      templatePathArgument, modelPathArgument, outputPathArgument, sourceFilesArgument);

    return rootCommand.Invoke(args);
  }

  private static List<(string, string)> ParseRewrites(ArgumentResult result) {
    var parsed = new List<(string, string)>();

    foreach (var tok in result.Tokens) {
      var split = tok.Value.Split(":");
      if (split.Length != 2) {
        result.ErrorMessage = "--rewrite takes a pair of strings separated by `:`";
      }
      parsed.Add((split[0], split[1]));
    }

    return parsed;
  }

  private static void ParsedMain(
    string projectPath, string rootModule, List<(string, string)> nameRewrites, IList<string> skippedInterfaces,
    string templatePath, string modelPath, string outputPath, List<string> sourceFiles
  ) {
    nameRewrites.Add((rootModule + ".", ""));

    var rewriter = new SimpleNameRewriter(nameRewrites);
    var dafnyCode = GenerateDafnyCode(projectPath, sourceFiles, rootModule, rewriter, skippedInterfaces);
    var template = ReadTemplate(templatePath);

    // Add \n to allow the line that contains the placeholder to be commented out
    File.WriteAllText(outputPath, template.Replace(Placeholder, "\n" + dafnyCode), Encoding.UTF8);

    CopyCSharpModel(modelPath);
  }
}
