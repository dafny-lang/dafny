using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Text.RegularExpressions;
using System.Text;

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

  public static string eol = "\n";

  public static DafnyDriver.ExitValue DoDocumenting(IList<DafnyFile> dafnyFiles, List<string> dafnyFolders,
    ErrorReporter reporter, string programName, DafnyOptions options) {

    // Optional behaviors: clear directory
    // Make a tree or flat directory
    string outputdir = null;
    if (outputdir == null) outputdir = "./docs";
    if (Directory.Exists(outputdir)) {
      Directory.Delete(outputdir, true);
    }
    var d = Directory.CreateDirectory(outputdir);

    var exitValue = DafnyDriver.ExitValue.SUCCESS;
    //Contracts.Assert(dafnyFiles.Count > 0 || dafnyFolders.Count > 0);
    dafnyFiles = dafnyFiles.Concat(dafnyFolders.SelectMany(folderPath => {
      return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
          .Select(name => new DafnyFile(name)).ToList();
    })).ToList();
    Console.Out.Write($"Documenting {dafnyFiles.Count} files from {dafnyFolders.Count} folders\n");
    if (dafnyFiles.Count == 0) return exitValue;

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
    AddToIndexF(module.Name, fullName, "module");
    bool formatIsHtml = true;
    var defaultClass = moduleDef.TopLevelDecls.Where(d => d is ClassDecl && (d as ClassDecl).IsDefaultClass).ToList()[0] as ClassDecl;
    if (formatIsHtml) {
      var contentslink = "<a href=\"index.html\">[table of contents]</a>";
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
      var docstring = Docstring(module);
      var shortstring = ShortDocstring(module);
      if (!String.IsNullOrEmpty(docstring)) {
        file.Write(shortstring);
        if (shortstring != docstring) {
          file.Write(" <a href=\"#module-detail\">(more...)</a>");
        }
        file.Write(br);
        file.Write(br);
        file.Write(br);
        file.Write(eol);
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
      StringBuilder summaries = new StringBuilder(1000);
      StringBuilder details = new StringBuilder(1000);
      WriteExports(moduleDef, summaries, details);
      WriteImports(moduleDef, summaries, details);
      WriteSubModules(moduleDef, summaries, details);
      WriteTypes(moduleDef, summaries, details);
      WriteConstants(defaultClass, summaries, details);
      WriteFunctions(defaultClass, summaries, details);
      WriteMethods(defaultClass, summaries, details);
      WriteLemmas(defaultClass, summaries, details);
      file.WriteLine(summaries.ToString());
      file.WriteLine(Heading2("module details\n"));
      file.WriteLine("<a id=\"module-detail\"/>");
      file.WriteLine(docstring);
      file.WriteLine(eol + br + br + eol);
      file.WriteLine(details.ToString());
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
    AddToIndexF(decl.Name, fullName, decl.WhatKind);
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
      var indexlink = "<a href=\"nameindex.html\">[index]</a>";
      file.WriteLine($"<div>\n<h1>{abs}class {QualifiedNameWithLinks(fullName, false)}{extends}{space4}{Smaller(indexlink)}</h1>\n</div>");
      file.Write(bodystart);
      string declFilename = decl.Tok.Filename;
      file.WriteLine($"From file: {declFilename}" + br);
      //var modifyTime = File.GetLastWriteTime(moduleFilename);
      //file.WriteLine($"Last modified: {modifyTime}" + br);

      // TODO _ types in a class?
      StringBuilder summaries = new StringBuilder(1000);
      StringBuilder details = new StringBuilder(1000);
      WriteConstants(decl, summaries, details);
      WriteMutableFields(decl, summaries, details);
      WriteFunctions(decl, summaries, details);
      WriteMethods(decl, summaries, details);
      WriteLemmas(decl, summaries, details);
      file.WriteLine(summaries.ToString());
      file.Write(foot);
      AnnounceFile(filename);
    }
  }

  public void WriteExports(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {

    var exports = module.TopLevelDecls.Where(d => d is ModuleExportDecl).Select(d => d as ModuleExportDecl);
    summaries.Append(Heading3("Export sets")).Append(eol);
    details.Append(Heading3("Export sets")).Append(eol);
    if (exports.Count() == 0) {
      var text = $"export {Bold(module.Name + "`" + module.Name)} : reveals *";
      summaries.Append(text).Append(eol);
      details.Append(text).Append(eol);
    } else {
      foreach (var ex in exports) {
        var text = $"export {Bold(module.Name + "`" + ex.Name)}";
        summaries.Append(text).Append(br).Append(eol);
        details.Append(text).Append(br).Append(eol);
        details.Append("&nbsp;&nbsp;&nbsp;&nbsp;");
        foreach (var id in ex.Exports) { // TODO - make thiese ids into links
          details.Append(" ").Append(id.Id);
        }
        details.Append(br).Append(eol);
      }
    }
  }

  public void WriteImports(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {
    var imports = module.TopLevelDecls.Where(d => d is AliasModuleDecl).Select(d => d as AliasModuleDecl).ToList();
    imports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    var absimports = module.TopLevelDecls.Where(d => d is AbstractModuleDecl).Select(d => d as AbstractModuleDecl).ToList();
    absimports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (imports.Count() + absimports.Count() > 0) {
      summaries.Append(Heading3("Imports")).Append(eol);
      foreach (var imp in imports) {
        var name = imp.Name;
        var target = imp.Dereference();
        summaries.Append($"import {name} = {QualifiedNameWithLinks(target.FullDafnyName)}").Append(eol);
      }
      foreach (var imp in absimports) {
        var name = imp.Name;
        var target = imp.QId; // TODO - is this fully quallified
        summaries.Append($"import {name} : {QualifiedNameWithLinks(target.ToString())}").Append(eol);
      }
    }
  }

  public void WriteSubModules(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {
    var submods = module.TopLevelDecls.Where(d => d is LiteralModuleDecl).Select(d => d as LiteralModuleDecl).ToList();
    submods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (submods.Count() > 0) {
      summaries.Append(Heading3("Submodules")).Append(eol);
      foreach (var submod in submods) {
        summaries.Append("module ").Append(QualifiedNameWithLinks(submod.FullDafnyName)).Append(br).Append(eol);
      }
    }
  }

  public void WriteTypes(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {
    var types = module.TopLevelDecls.Where(c => c is RevealableTypeDecl).ToList(); // TODO - what kind of types does this leave out?
    types.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (types.Count() > 0) {
      summaries.Append(Heading3("Types")).Append(eol);
      summaries.Append("<table>\n");
      foreach (var t in types) {
        if ((t is ClassDecl) && (t as ClassDecl).IsDefaultClass) continue;
        summaries.Append("<tr>\n");
        summaries.Append("<td>");
        summaries.Append(t.WhatKind);
        summaries.Append("</td>");
        summaries.Append("<td>");
        if (ShouldMakeSeparatePage(t)) {
          summaries.Append(Link(t.FullDafnyName, Bold(t.Name))).Append(eol); // Only link types with members - check this
        } else if (t is ClassDecl || t is TraitDecl) {
          summaries.Append(Bold(t.Name) + "{}\n");
        } else {
          summaries.Append(Bold(t.Name)).Append(eol);
        }
        summaries.Append("</td></tr>\n");
      }
      summaries.Append("</table>\n");
    }
  }

  public void WriteConstants(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var constants = decl.Members.Where(c => c is ConstantField).Select(c => c as ConstantField).ToList();
    constants.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (constants.Count() > 0) {
      summaries.Append(Heading3("Constants\n"));
      details.Append(Heading3("Constants\n"));
      // TODO: opaque, ghost, init, link for type

      foreach (var c in constants) {
        AddToIndex(c.Name, decl.FullDafnyName, "const");
        summaries.Append(LinkToAnchor(c.Name, Bold(c.Name))).Append(": ").Append(TypeLink(c.Type));
        var docstring = ShortDocstring(c);
        var modifiers = Modifiers(c);
        var attributes = Attributes(c.Attributes);
        if (!String.IsNullOrEmpty(docstring)) {
          summaries.Append(" &mdash; ").Append(docstring);
        }
        summaries.Append(br).Append(eol);
        details.Append(Anchor(c.Name)).Append(eol);
        if (!String.IsNullOrEmpty(modifiers)) {
          details.Append(modifiers).Append(br).Append(eol);
        }
        details.Append(Bold(c.Name)).Append(": ").Append(TypeLink(c.Type));
        if (c.Rhs != null) {
          details.Append(" := ").Append(c.Rhs.ToString()); // TODO - other kinds of initialization?
        }
        details.Append(br).Append(eol);
        if (!String.IsNullOrEmpty(attributes)) {
          details.Append(space4).Append(attributes).Append(br).Append(eol);
        }
        docstring = ShortDocstring(c);
        if (!String.IsNullOrEmpty(docstring)) {
          details.Append(indent).Append(docstring).Append(unindent).Append(eol);
        }
      }
    }
  }

  public bool ShouldMakeSeparatePage(Declaration t) {
    return t is TopLevelDeclWithMembers && (t as TopLevelDeclWithMembers).Members.Count() > 0;
  }

  public void WriteMutableFields(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var fields = decl.Members.Where(c => c is Field && c is not ConstantField).Select(c => c as Field).ToList();
    fields.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (fields.Count() > 0) {
      summaries.Append(Heading3("Mutable Fields\n"));
      details.Append(Heading3("Mutable Fields\n"));
      // TODO: opaque, ghost, link for type

      summaries.Append(BeginTable()).Append(eol);
      bool first = true;
      foreach (var c in fields) {
        AddToIndex(c.Name, decl.FullDafnyName, "var");
        if (first) {
          first = false;
        } else {
          summaries.Append(Row()).Append(eol);
        }
        var modifiers = Modifiers(c);
        var attrs = Attributes(c.Attributes);
        string doc = ShortDocstring(c);
        summaries.Append(Anchor(c.Name)).Append(eol);
        summaries.Append(Row(modifiers, Bold(c.Name), ":", TypeLink(c.Type), "&mdash;", doc)).Append(eol);
        doc = Docstring(c);
        details.Append(Row(modifiers, Bold(c.Name), ":", TypeLink(c.Type), "", "Attributes: " + attrs)).Append(eol);
        details.Append(Row("", "", "", "", "&mdash;", doc)).Append(eol);
      }
      summaries.Append(EndTable()).Append(eol);
      summaries.Append(br).Append(eol);
      details.Append(EndTable()).Append(eol);
      details.Append(br).Append(eol);
    }
  }

  public void WriteFunctions(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var functions = decl.Members.Where(m => m is Function).Select(m => m as Function).ToList();
    functions.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (functions.Count > 0) {
      summaries.Append(Heading3("Functions")).Append(eol);
      foreach (var f in functions) {
        AddToIndex(f.Name, decl.FullDafnyName, f.WhatKind);
        var modifiers = Modifiers(f);
        var attributes = Attributes(f.Attributes);
        var typeparams = TypeArgs(f.TypeArgs);
        summaries.Append(f.GetFunctionDeclarationKeywords(Options)).Append(" ");
        summaries.Append(Bold(f.Name)).Append(typeparams).Append("(").Append(String.Join(", ", f.Formals.Select(a => a.ToString()))).Append(")");
        summaries.Append(": ").Append(f.ResultType.ToString());
        summaries.Append(br).Append(eol);
      }
    }
  }

  public void WriteMethods(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var methods = decl.Members.Where(m => m is Method && m is not Lemma).Select(m => m as Method).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      summaries.Append(Heading3("Methods")).Append(eol);
      details.Append(Heading3("Methods")).Append(eol);
      foreach (var m in methods) {
        var modifiers = Modifiers(m);
        AddToIndex(m.Name, decl.FullDafnyName, "method");
        summaries.Append(modifiers).Append(br).Append(eol);
        summaries.Append(Bold(m.Name)).Append(br).Append(br).Append(eol);
        details.Append(modifiers).Append(br).Append(eol);
        details.Append(Bold(m.Name)).Append(br).Append(br).Append(eol);
        // TODO Needs attributes, needs specs
        foreach (var req in m.Req) {
          details.Append(space4).Append("requires ").Append(req.ToString()).Append(br).Append(eol);
        }
        //foreach (var mod in m.Mod) {
        // TODO details.Append(space4).Append("modifies ").Append(mod.ToString()).Append(br).Append(eol);
        //}
        foreach (var en in m.Ens) {
          details.Append(space4).Append("ensures ").Append(en.ToString()).Append(br).Append(eol);
        }
        if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
          var dec = String.Join(", ", m.Decreases.Expressions.Select(e => e.ToString()));
          details.Append(space4).Append("decreases ").Append(dec).Append(br).Append(eol);
        }
      }
    }
  }

  string MethodSig(Method m) {
    var typeparams = TypeArgs(m.TypeArgs);
    var formals = String.Join(", ", m.Ins.Select(f => f.ToString()));
    var outformals = String.Join(", ", m.Outs.Select(f => f.ToString()));
    if (outformals.Length != 0) outformals = " returns (" + outformals + ")";
    return Bold(m.Name) + typeparams + "(" + formals + ")" + outformals;
  }

  public void WriteLemmas(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var methods = decl.Members.Where(m => m is Lemma).Select(m => m as Lemma).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      summaries.Append(Heading3("Lemmas")).Append(eol);
      details.Append(Heading3("Lemmas")).Append(eol);
      foreach (var m in methods) {
        var ms = MethodSig(m);
        AddToIndex(m.Name, decl.FullDafnyName, m.WhatKind);
        summaries.Append(ms).Append(br).Append(br).Append(eol);
        details.Append(ms).Append(br).Append(br).Append(eol);
        var attr = Attributes(m.Attributes);
        if (!String.IsNullOrEmpty(attr)) details.Append(space4).Append(Attributes(m.Attributes)).Append(br).Append(eol);
        var docstring = Docstring(m);
        if (!String.IsNullOrEmpty(docstring)) details.Append(indent).Append(docstring).Append(unindent).Append(eol);
        foreach (var req in m.Req) {
          details.Append(space4).Append("requires ").Append(req.E.ToString()).Append(br).Append(eol);
        }
        //foreach (var mod in m.Mod) {
        // TODO details.Append(space4).Append("modifies ").Append(mod.ToString()).Append(br).Append(eol);
        //}
        foreach (var en in m.Ens) {
          details.Append(space4).Append("ensures ").Append(en.E.ToString()).Append(br).Append(eol);
        }
        if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
          var dec = String.Join(", ", m.Decreases.Expressions.Select(e => e.ToString()));
          details.Append(space4).Append("decreases ").Append(dec).Append(br).Append(eol);
        }
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
      file.Write($"<div>\n<h1>Dafny Program: {DafnyProgram.Name}&nbsp;&nbsp;&nbsp;&nbsp;{Smaller(indexlink)}</h1>\n</div>");
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

  public void AddToIndexF(string name, string target, string kind) {
    nameIndex.Add(name + " " + nameIndex.Count + " " + target, kind + " " + QualifiedNameWithLinks(target));
  }

  public void AddToIndex(string name, string owner, string kind) {
    var target = owner + "#" + name;
    nameIndex.Add(name + " " + nameIndex.Count + " " + owner, kind + " " + QualifiedNameWithLinks(target));
  }

  public string Docstring(IHasDocstring d) {
    var ds = d.GetDocstring(DafnyProgram.Options);
    if (ds == null) return String.Empty;
    return ds.Trim();
  }

  public string ShortDocstring(IHasDocstring d) {
    var ds = Docstring(d);
    return Shorten(ds);
  }

  public string Shorten(string docstring) {
    if (docstring == null) return String.Empty;
    var k = docstring.IndexOf('.');
    if (k == -1) return docstring;
    return docstring.Substring(0, k + 1);
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
    int hash = fullName.IndexOf('#');
    string tail = null;
    if (hash > 0) {
      tail = fullName.Substring(hash + 1);
      fullName = fullName.Substring(0, hash);
    }
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
    if (hash > 0) {
      output += $".<a href=\"{fullName}.html#{tail}\">{tail}</a>";
    }
    return output;
  }

  public static string Link(string fullName, string text) {
    return $"<a href=\"{fullName}.html\">{text}</a>";
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

  public String Anchor(string name) {
    return $"<a id=\"{name}\"/>";
  }

  public String LinkToAnchor(string name, string text) {
    return $"<a href=\"#{name}\">{text}</a>";
  }

  public String Mdash = " &mdash; ";

  public string Modifiers(MemberDecl d) {
    string result = "";
    if (d.IsGhost) result += "ghost ";
    //if (d.IsAbstract) result += "abstract ";
    if (d.IsStatic) result += "static ";
    if (d.IsOpaque) result += "opaque ";
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
        var exprs = String.Join(", ", attribute.Args.Select(e => e.ToString()));
        return result + " " + exprs + "}";
      }
    }
  }

  public string TypeArgs(List<TypeParameter> args) {
    if (args.Count == 0) return "";
    return "&lt;" + String.Join(",", args.Select(a => a.ToString())) + "&gt;";
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
      // The 'key' is the element name + space + a uniqueifying integer
      var k = key.IndexOf(' ');
      var value = nameIndex[key]; // Already rewritten as a bunch of links
      var keyn = key.Substring(0, k);
      k = key.LastIndexOf(' ');
      var owner = key.Substring(k + 1);
      var hash = value.IndexOf('#');
      if (hash != -1) {
        var link = value.Substring(0, hash);
        file.Write($"<a href=\"{owner}.html#{keyn}\">{keyn}</a>");
      } else {
        file.Write($"<a href=\"{owner}.html\">{keyn}</a>");
      }
      file.WriteLine(" &mdash; " + value + br);
    }
    file.Write(foot);
  }

  static string br = "<br>";

  static string space4 = "&nbsp;&nbsp;&nbsp;&nbsp;";

  static string indent = "<p style=\"margin-left: 25px;\">";
  static string unindent = "</p>";
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

