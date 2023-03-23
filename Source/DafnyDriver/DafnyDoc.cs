using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny;

/* Stuff todo:
- Better sizing of text in h1 headings
- modules: modifiers, fully qualified refinement
- exports - list provides and reveals
- default exports -- list all available names?
- abstract imports - needs fully qualified target
- in each section , list inherited names, import-opened names
- all types everywhere - link to relevant target
- types - modifiers, show content of definition, link to separate page if there are members
- constants - modifies and initalizer
- fields - modifiers 
- methods - modifiers, signature, specifications
- constructors - modifiers, signature, specifications
- functions - modifiers, signature, specifications
- lemmas  - modifiers, signature, specifications

--- Docstrings????

- don't always make the last segment of a qualified name linkable
- add type arguments everywhere
- add attributes everywhere
- make ghost italics?
- make sure we have resolved types
- do not include library files
- separate css file; also add the dafny favicon

- known subtypes of traits

*/

class DafnyDoc {

  public static DafnyDriver.ExitValue DoDocumenting(IList<DafnyFile> dafnyFiles, List<string> dafnyFolders,
    ErrorReporter reporter, string programName, DafnyOptions options) {

    // Optional behaviors: clear directory
    // Make a tree or flat directory
    string outputdir = null;
    if (outputdir == null) outputdir = "./docs";
    Directory.Delete(outputdir, true);
    var d = Directory.CreateDirectory(outputdir);

    var exitValue = DafnyDriver.ExitValue.SUCCESS;
    String result = "";
    //Contracts.Assert(dafnyFiles.Count > 0 || dafnyFolders.Count > 0);
    dafnyFiles = dafnyFiles.Concat(dafnyFolders.SelectMany(folderPath => {
      return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
          .Select(name => new DafnyFile(name)).ToList();
    })).ToList();
    Console.Out.Write($"Documenting {dafnyFiles.Count} files from {dafnyFolders.Count} folders\n");

    string err = null;
    Program dafnyProgram = null;
    try {
      err = Dafny.Main.ParseCheck(dafnyFiles, programName, reporter, out dafnyProgram);
    } catch (Exception e) {
      err = "Exception while parsing -- please report the error (use --verbose to see the call stack)";
      if (options.CompileVerbose) {
        Console.Out.WriteLine(e.ToString());
      }
    }
    if (err != null) {
      exitValue = DafnyDriver.ExitValue.DAFNY_ERROR;
      Console.Error.WriteLine(err);
    } else {
      Contract.Assert(dafnyProgram != null);

      new DafnyDoc(dafnyProgram, reporter, options, outputdir).GenerateDocs(dafnyFiles);

    }
    return exitValue;
  }

  public Program DafnyProgram;
  public ErrorReporter Reporter;
  public DafnyOptions Options;
  public string Outputdir;
  public Dictionary<string, string> nameIndex = new Dictionary<string, string>();

  public DafnyDoc(Program dafnyProgram, ErrorReporter reporter, DafnyOptions options, string outputdir) {
    this.DafnyProgram = dafnyProgram;
    this.Reporter = reporter;
    this.Options = options;
    this.Outputdir = outputdir;
  }

  public void GenerateDocs(IList<DafnyFile> dafnyFiles) {
    var modDecls = new List<LiteralModuleDecl>();
    CollectDecls(DafnyProgram.DefaultModule as LiteralModuleDecl, modDecls);
    WriteTOC(modDecls);
    foreach (var m in modDecls) {
      WriteModule(m);
    }
    WriteIndex();
  }

  public void CollectDecls(LiteralModuleDecl mod, List<LiteralModuleDecl> modDecls) {
    modDecls.Add(mod);
    foreach (var d in mod.ModuleDef.TopLevelDecls) {
      if (d is LiteralModuleDecl) CollectDecls(d as LiteralModuleDecl, modDecls);
    }
  }

  public void WriteModule(LiteralModuleDecl module) {
    var moduleDef = module.ModuleDef;
    var fullName = moduleDef.FullDafnyName;
    nameIndex.Add(module.Name + " " + nameIndex.Count, "module " + QualifiedNameWithLinks(fullName));
    bool formatIsHtml = true;
    var defaultClass = moduleDef.TopLevelDecls.Where(d => d is ClassDecl && (d as ClassDecl).IsDefaultClass).ToList()[0] as ClassDecl;
    if (formatIsHtml) {
      var contentslink = "<a href=\"index.html\">[table of contents]</a><br><br>";
      var indexlink = "<a href=\"nameindex.html\">[index]</a>";
      string filename = Outputdir + "/" + moduleDef.FullDafnyName + ".html";
      using StreamWriter file = new(filename);
      file.Write(head1);
      file.Write($"Module {fullName} in program {DafnyProgram.Name}");
      file.Write(head2);
      file.Write(style);
      var abs = moduleDef.IsAbstract ? "abstract " : "";
      file.WriteLine($"<div>\n<h1>{abs}module {QualifiedNameWithLinks(fullName, false)}&nbsp;&nbsp;&nbsp;{Smaller(contentslink + indexlink)}</h1>\n</div>");
      file.Write(bodystart);
      var docstring = module.GetDocstring(DafnyProgram.Options);
      if (!String.IsNullOrEmpty(docstring)) {
        file.WriteLine(docstring);
        file.Write(br);
        file.Write(br);
      }
      if (moduleDef.RefinementQId != null) {
        file.WriteLine("refines " + QualifiedNameWithLinks(moduleDef.RefinementQId.ToString()) + br); // TODO - RefinementQID is not fully qualified
      }
      var attributes = Attributes(moduleDef.Attributes);
      if (!String.IsNullOrEmpty(attributes)) {
        file.WriteLine("Attributes: " + attributes + br);
      }

      string moduleFilename = module.Tok.Filename;
      file.WriteLine($"From file: {moduleFilename}" + br);
      //var modifyTime = File.GetLastWriteTime(moduleFilename);
      //file.WriteLine($"Last modified: {modifyTime}" + br);

      file.WriteLine(Heading2("module summary"));
      WriteExports(file, moduleDef);
      WriteImports(file, moduleDef);
      WriteSubModules(file, moduleDef);
      WriteTypes(file, moduleDef);
      WriteConstants(file, moduleDef);
      WriteFunctions(file, defaultClass);
      WriteMethods(file, defaultClass);
      WriteLemmas(file, defaultClass);
      file.WriteLine(Heading2("module details"));
      file.Write(foot);
      AnnounceFile(filename);
      var declsWithMembers = moduleDef.TopLevelDecls.Where(c => c is TopLevelDeclWithMembers).Select(c => c as TopLevelDeclWithMembers).ToList();
      foreach (var c in declsWithMembers) {
        if (c is not ClassDecl) continue; // TODO : handle these later
        var cl = c as ClassDecl;
        if (cl.IsDefaultClass) continue;
        WriteDecl(c);
      }
    }
  }

  public void WriteDecl(TopLevelDeclWithMembers decl) {
    var fullName = decl.FullDafnyName;
    nameIndex.Add(decl.Name + " " + nameIndex.Count, decl.WhatKind + " " + QualifiedNameWithLinks(fullName));
    bool formatIsHtml = true;
    if (formatIsHtml) {
      string filename = Outputdir + "/" + fullName + ".html";
      using StreamWriter file = new(filename);
      file.Write(head1);
      file.Write($"{decl.WhatKind} {fullName}");
      file.Write(head2);
      file.Write(style);
      var abs = "";//decl.IsAbstract ? Smaller("abstract ") : ""; // TODO - smaller is too much smaller for h1
      var extends = "";
      if (decl.ParentTraits != null && decl.ParentTraits.Count() > 0) {
        extends = Smaller(" extends ..."); // TODO - fill in with links, transitive list?
      }
      file.WriteLine($"<div>\n<h1>{abs}class {QualifiedNameWithLinks(fullName, false)}{extends}</h1>\n</div>");
      file.Write(bodystart);
      string declFilename = decl.Tok.Filename;
      file.WriteLine($"From file: {declFilename}" + br);
      //var modifyTime = File.GetLastWriteTime(moduleFilename);
      //file.WriteLine($"Last modified: {modifyTime}" + br);

      // TODO _ types in a class?
      //WriteConstants(file, decl);
      WriteMutableFields(file, decl);
      WriteFunctions(file, decl);
      WriteMethods(file, decl);
      WriteLemmas(file, decl);
      file.Write(foot);
      AnnounceFile(filename);
    }
  }

  public void WriteExports(StreamWriter file, ModuleDefinition module) {
    var exports = module.TopLevelDecls.Where(d => d is ModuleExportDecl).Select(d => d as ModuleExportDecl);
    file.WriteLine(Heading3("Export sets"));
    if (exports.Count() == 0) {
      file.WriteLine("export " + Bold(module.Name + "`" + module.Name) + " : reveals *");
    } else {
      foreach (var ex in exports) {
        file.WriteLine("export " + Bold(module.Name + "`" + ex.Name) + br);
        file.Write("&nbsp;&nbsp;&nbsp;&nbsp;");
        foreach (var id in ex.Exports) {
          file.Write(" " + id.Id);
        }
        file.WriteLine(br);
      }
    }
  }

  public void WriteImports(StreamWriter file, ModuleDefinition module) {
    var imports = module.TopLevelDecls.Where(d => d is AliasModuleDecl).Select(d => d as AliasModuleDecl).ToList();
    imports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    var absimports = module.TopLevelDecls.Where(d => d is AbstractModuleDecl).Select(d => d as AbstractModuleDecl).ToList();
    absimports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (imports.Count() + absimports.Count() > 0) {
      file.WriteLine(Heading3("Imports"));
      foreach (var imp in imports) {
        var name = imp.Name;
        var target = imp.Dereference();
        file.WriteLine($"import {name} = {QualifiedNameWithLinks(target.FullDafnyName)}");
      }
      foreach (var imp in absimports) {
        var name = imp.Name;
        var target = imp.QId; // TODO - is this fully quallified
        file.WriteLine($"import {name} : {QualifiedNameWithLinks(target.ToString())}");
      }
    }
  }

  public void WriteSubModules(StreamWriter file, ModuleDefinition module) {
    var submods = module.TopLevelDecls.Where(d => d is LiteralModuleDecl).Select(d => d as LiteralModuleDecl).ToList();
    submods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (submods.Count() > 0) {
      file.WriteLine(Heading3("Submodules"));
      foreach (var submod in submods) {
        file.WriteLine("module " + QualifiedNameWithLinks(submod.FullDafnyName) + br);
      }
    }
  }

  public void WriteTypes(StreamWriter file, ModuleDefinition module) {
    var types = module.TopLevelDecls.Where(c => c is RevealableTypeDecl).ToList(); // TODO - what kind of types does this leave out?
    types.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (types.Count() > 0) {
      file.WriteLine(Heading3("Types"));
      file.WriteLine("<table>");
      foreach (var t in types) {
        if ((t is ClassDecl) && (t as ClassDecl).IsDefaultClass) continue;
        file.WriteLine("<tr>");
        file.Write("<td>");
        file.Write(t.WhatKind);
        file.Write("</td>");
        file.Write("<td>");
        if (ShouldMakeSeparatePage(t)) {
          file.WriteLine(Link(t.FullDafnyName, Bold(t.Name))); // Only link types with members - check this
        } else if (t is ClassDecl || t is TraitDecl) {
          file.WriteLine(Bold(t.Name) + "{}");
        } else {
          file.WriteLine(Bold(t.Name));
        }
        file.Write("</td>");
        file.WriteLine("</tr>");
      }
      file.WriteLine("</table>");
    }

  }

  public void WriteConstants(StreamWriter file, ModuleDefinition module) {
    var constants = ModuleDefinition.AllFields(module.TopLevelDecls).Where(c => c is ConstantField).ToList();
    constants.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (constants.Count() > 0) {
      file.WriteLine(Heading3("Constants"));
      // TODO: opaque, ghost, init, link for type

      foreach (var c in constants) {
        file.Write(Bold(c.Name) + ": " + TypeLink(c.Type));
        //        if (c.Init != null) {
        //         file.Write(" := ");
        //          file.Write(c.Init.ToString());
        //        }
        file.WriteLine(br);
      }
    }
  }

  public bool ShouldMakeSeparatePage(Declaration t) {
    return t is TopLevelDeclWithMembers && (t as TopLevelDeclWithMembers).Members.Count() > 0;
  }

  public void WriteMutableFields(StreamWriter file, TopLevelDeclWithMembers decl) {
    var fields = decl.Members.Where(c => c is Field && c is not ConstantField).Select(c => c as Field).ToList();
    fields.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (fields.Count() > 0) {
      file.WriteLine(Heading3("Mutable Fields"));
      // TODO: opaque, ghost, link for type

      file.WriteLine(BeginTable());
      bool first = true;
      foreach (var c in fields) {
        if (first) {
          first = false;
        } else {
          file.WriteLine(Row());
        }
        var modifiers = Modifiers(c);
        var attrs = Attributes(c.Attributes);
        string doc = "Just some information about " + c.Name;
        if (attrs.Length == 0) {
          file.WriteLine(Row(modifiers, Bold(c.Name), ":", TypeLink(c.Type), "&mdash;", doc));
        } else {
          file.WriteLine(Row(modifiers, Bold(c.Name), ":", TypeLink(c.Type), "", "Attributes: " + attrs));
          file.WriteLine(Row("", "", "", "", "&mdash;", doc));
        }
      }
      file.WriteLine(EndTable());
      file.WriteLine(br);
    }
  }

  public void WriteFunctions(StreamWriter file, TopLevelDeclWithMembers decl) {
    var functions = decl.Members.Where(m => m is Function).Select(m => m as Function).ToList();
    functions.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (functions.Count > 0) {
      file.WriteLine(Heading3("Functions"));
      foreach (var f in functions) {
        file.WriteLine(f.GetFunctionDeclarationKeywords(Options) + " " + Bold(f.Name) + br);
      }
    }
  }

  public void WriteMethods(StreamWriter file, TopLevelDeclWithMembers decl) {
    var methods = decl.Members.Where(m => m is Method && m is not Lemma).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      file.WriteLine(Heading3("Methods"));
      foreach (var m in methods) {
        file.WriteLine((m.IsGhost ? "ghost " : "") + (m.IsStatic ? "static " : "") + br);
        file.WriteLine(Bold(m.Name) + br + br);
        // TODO Needs attributes, needs specs
      }
    }
  }

  public void WriteLemmas(StreamWriter file, TopLevelDeclWithMembers decl) {
    var methods = decl.Members.Where(m => m is Lemma).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      file.WriteLine(Heading3("Lemmas"));
      foreach (var m in methods) {
        file.WriteLine(Bold(m.Name) + br + br);
        // TODO Needs attributes, needs specs, static?
      }
    }
  }

  public void WriteTOC(List<LiteralModuleDecl> mdecls) {
    bool formatIsHtml = true;
    mdecls.Sort((k, m) => k.FullDafnyName.CompareTo(m.FullDafnyName));
    if (formatIsHtml) {
      string filename = Outputdir + "/index.html";
      using StreamWriter file = new(filename);
      file.Write(head1);
      file.Write($"Modules in program {DafnyProgram.Name}");
      file.Write(head2);
      file.Write(style);
      var indexlink = "<a href=\"nameindex.html\">[index]</a>";
      file.Write($"<div>\n<h1>Dafny Program: {DafnyProgram.Name}&nbsp;&nbsp'&nbsp;&nbsp;{Smaller(indexlink)}</h1>\n</div>");
      file.Write(bodystart);
      file.WriteLine("<ul>");
      int currentIndent = 0;
      foreach (var decl in mdecls) {
        var name = decl.FullDafnyName;
        if (name.Length == 0) name = "_";
        int level = Regex.Matches(name, "\\.").Count;
        while (level > currentIndent) {
          file.WriteLine("<ul>");
          currentIndent++;
        }
        while (level < currentIndent) {
          file.WriteLine("</ul>");
          currentIndent--;
        }
        var ds = ShortDocstring(decl).Trim();
        if (ds.Length > 0) ds = " &mdash; " + ds;
        file.WriteLine($"<li>Module <a href=\"{name}.html\">{name}</a>" + ds + "</li>");
      }
      file.WriteLine("</ul>");
      file.Write(foot);
      AnnounceFile(filename);
    }
  }

  public static string TypeLink(Type t) {
    if (t is BasicType || t is CollectionType) {
      return t.ToString();
    } else if (t is UserDefinedType && (t as UserDefinedType).ResolvedClass is ClassDecl) {
      return Link((t as UserDefinedType).ResolvedClass.FullDafnyName, "" + t); // TODO - need to do links for type args also
    } else {
      return t.ToString();
    }
  }

  public string ShortDocstring(IHasDocstring d) {
    var ds = d.GetDocstring(DafnyProgram.Options);
    if (ds == null) return String.Empty;
    var k = ds.IndexOf('.');
    if (k == -1) return ds;
    return ds.Substring(0, k + 1);
  }

  public static string Heading2(string text) {
    return "<div>\n<h2>" + text + "</h2>\n</div>";
  }

  public static string Heading3(string text) {
    return "<div>\n<h3>" + text + "</h3>\n</div>";
  }

  public static string Smaller(string text) {
    return $"<font size=\"-1\">{text}</font>";
  }

  public static string Bold(string text) {
    return $"<b>{text}</b>";
  }

  public static string QualifiedNameWithLinks(string fullName, bool alsoLast = true) {
    var names = fullName.Split('.');
    string nameSoFar = "";
    string output = "";
    int k = names.Length;
    foreach (string name in names) {
      if (names.Length != k) {
        output += ".";
        nameSoFar += ".";
      }
      k--;
      nameSoFar += name;
      output += (k == 0 && !alsoLast ? name : Link(nameSoFar, name));
    }
    return output;
  }

  public static string Link(string fullName, string text) {
    return "<a href=\"" + fullName + ".html\">" + text + "</a>";
  }

  public string BeginTable() {
    return "<table>";
  }

  public string Row() {
    return $"<tr></tr>";
  }

  public string Row(string s1, string s2) {
    return $"<tr><td>{s1}</td><td>{s2}</td></tr>";
  }

  public string Row(string s1, string s2, string s3) {
    return $"<tr><td>{s1}</td><td>{s2}</td><td>{s3}</td></tr>";
  }

  public string Row(string s1, string s2, string s3, string s4) {
    return $"<tr><td>{s1}</td><td>{s2}</td><td>{s3}</td><td>{s4}</td></tr>";
  }

  public string Row(string s1, string s2, string s3, string s4, string s5) {
    return $"<tr><td>{s1}</td><td>{s2}</td><td>{s3}</td><td>{s4}</td><td>{s5}</td></tr>";
  }

  public string Row(string s1, string s2, string s3, string s4, string s5, string s6) {
    return $"<tr><td>{s1}</td><td>{s2}</td><td>{s3}</td><td>{s4}</td><td>{s5}</td><td>{s6}</td></tr>";
  }

  public String EndTable() {
    return "</table>";
  }

  public string Modifiers(object d) { //Member d) {
    string result = "<mods>";
    // if (d.IsGhost) result += "ghost ";
    // if (d.IsAbstract) result += "abstract ";
    // if (d.IsStatic) result += "static ";
    // if (d.IsOpaque) result += "opaque ";
    return result;
  }

  public string Attributes(Attributes attribute) {
    if (attribute == null) {
      return "";
    } else {
      string result = Attributes(attribute.Prev) + "{:" + attribute.Name;
      if (attribute.Args == null || attribute.Args.Count() == 0) {
        return result + "}";
      } else {
        // TODO - needs expressions
        return result + " " + "?" + "}";
      }
    }
  }

  public void AnnounceFile(string filename) {
    if (Options.CompileVerbose) {
      Console.WriteLine("Writing " + filename);
    }
  }

  public void WriteIndex() {
    var keys = nameIndex.Keys.ToList();
    keys.Sort();

    string filename = Outputdir + "/nameindex.html";
    using StreamWriter file = new(filename);
    file.Write(head1);
    file.Write($"Index for program {DafnyProgram.Name}");
    file.Write(head2);
    file.Write(style);
    file.Write($"<div>\n<h1>Index for Dafny Program: {DafnyProgram.Name}</h1>\n</div>");
    file.Write(bodystart);
    foreach (var key in keys) {
      var k = key.IndexOf(' ');
      file.WriteLine(key.Substring(0, k) + " &mdash; " + nameIndex[key] + br);
    }
    file.Write(foot);
  }

  public static string br = "<br>";

  public static string head1 =
  @"<!doctype html>

<html lang=""en"">
<head>
  <meta charset=""utf-8"">
  <meta name=""viewport"" content=""width=device-width, initial-scale=1"">

  <title>";

  public static string head2 =
  @"</title>
  <meta name=""description"" content=""Documentation for Dafny code produced by dafnydoc"">
  <meta name=""author"" content=""dafnydoc"">

  <link rel=""icon"" href=""dafny-favicon.ico"">
  <link rel=""icon"" href=""dafny-favicon.svg"" type=""image/svg+xml"">

</head>
";

  public static string style =
  @"<style>
body {
  background-color: white;
}

h1 {
  color: blue;
  text-align: center;
  background-color: #fceb6c
}
h2 {
  color: blue;
  text-align: left;
  background-color: #fceb6c
}
h3 {
  color: blue;
  text-align: left;
  background-color: #fceb6c
}

p {
  font-size: 16px
}
</style>
";

  public static string title =
  @"<div>
<h1>Dafny</h1>
</div>
";

  public static string bodystart =
  @"<body>
";

  public static string foot =
  @"</body>
</html>
";

}

