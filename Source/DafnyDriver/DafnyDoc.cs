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
- Should functions show body
- use table in nameindex
- cross reference
- name of root module
- page for root module, only when needed
- omit default decreases
- retain source layout of expressions
- table for all summary entries?
- modifiers (e.g. ghost) in summary entries?

- modules: modifiers, fully qualified refinement
- exports - list provides and reveals
- default exports -- list all available names?
- abstract imports - needs fully qualified target
- in each section , list inherited names, import-opened names
- types - modifiers, show content of definition, link to separate page if there are members
- constructors - modifiers, signature, specifications
- program name
- index entries for constructors

- don't always make the last segment of a qualified name linkable
- add type arguments everywhere
- add attributes everywhere
- make ghost italics?
- make sure we have resolved types
- do not include library files
- separate css file; also add the dafny favicon

- known subtypes of traits
- cross-reference

- overall visual design?
- separation into summary and details?

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

  // TODO _ combine with with WriteDecl
  public void WriteModule(LiteralModuleDecl module) {
    var moduleDef = module.ModuleDef;
    var fullName = moduleDef.FullDafnyName;
    AddToIndexF(module.Name, fullName, "module");
    bool formatIsHtml = true;
    var defaultClass = moduleDef.TopLevelDecls.Where(d => d is ClassDecl && (d as ClassDecl).IsDefaultClass).ToList()[0] as ClassDecl;
    if (formatIsHtml) {
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
        file.Write(ShortAndMoreForDecl(module));
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

      string moduleFilename = GetFileReference(module.Tok.Filename);
      if (moduleFilename != null) {
        file.WriteLine($"From file: {moduleFilename}" + br);
      }
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
      file.WriteLine("<a id=\"decl-detail\"/>");
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

  public string GetFileReference(string absoluteFile) {
    // absolute: return absoluteFile;
    // name: return GetFileName(absoluteFile);
    // none: return null;
    return Path.GetFileName(absoluteFile);
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
      file.WriteLine($"<div>\n<h1>{abs}class {QualifiedNameWithLinks(fullName, false)}{extends}{space4}{Smaller(contentslink + indexlink)}</h1>\n</div>");
      file.Write(bodystart);

      var docstring = Docstring(decl as IHasDocstring);
      var shortstring = Shorten(docstring);
      if (!String.IsNullOrEmpty(docstring)) {
        file.Write(ShortAndMoreForDecl(decl));
        file.Write(br);
        file.Write(br);
        file.Write(eol);
      }

      string declFilename = GetFileReference(decl.Tok.Filename);
      if (declFilename != null) {
        file.WriteLine($"From file: {declFilename}" + br);
        //var modifyTime = File.GetLastWriteTime(moduleFilename);
        //file.WriteLine($"Last modified: {modifyTime}" + br);
      }

      // TODO _ types in a class?
      StringBuilder summaries = new StringBuilder(1000);
      StringBuilder details = new StringBuilder(1000);
      if (decl is ClassDecl) {
        WriteConstructors(decl, summaries, details);
      }
      WriteConstants(decl, summaries, details);
      WriteMutableFields(decl, summaries, details);
      WriteFunctions(decl, summaries, details);
      WriteMethods(decl, summaries, details);
      WriteLemmas(decl, summaries, details);

      file.WriteLine(Heading2(decl.WhatKind + " summary"));
      //var modifyTime = File.GetLastWriteTime(moduleFilename);
      //file.WriteLine($"Last modified: {modifyTime}" + br);

      file.WriteLine(summaries.ToString());
      file.WriteLine("<a id=\"decl-detail\"/>");
      file.WriteLine(Heading2(decl.WhatKind + " details"));
      file.WriteLine(docstring);
      var attributes = Attributes(decl.Attributes);
      if (!String.IsNullOrEmpty(attributes)) {
        file.WriteLine("Attributes: " + attributes + br);
      }
      file.WriteLine(details.ToString());
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
        summaries.Append("module ").Append(QualifiedNameWithLinks(submod.FullDafnyName));
        var docstring = Docstring(submod);
        if (!String.IsNullOrEmpty(docstring)) {
          summaries.Append(Mdash);
          summaries.Append(Shorten(docstring));
        }
        summaries.Append(br).Append(eol);
      }
    }
  }

  public bool IsType(TopLevelDecl t) {
    return t is RevealableTypeDecl || t is SubsetTypeDecl;
  }

  public void WriteTypes(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {
    var types = module.TopLevelDecls.Where(c => IsType(c)).ToList(); // TODO - what kind of types does this leave out?
    types.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (types.Count() > 0) {
      summaries.Append(Heading3("Types")).Append(eol);
      summaries.Append("<table>\n");
      foreach (var t in types) {
        if ((t is ClassDecl) && (t as ClassDecl).IsDefaultClass) continue;
        var docstring = t is IHasDocstring ? Docstring(t as IHasDocstring) : "";
        var attributes = Attributes(t.Attributes);
        //var modifiers = Modifiers(t);
        summaries.Append("<tr>\n");
        summaries.Append("<td>");
        summaries.Append(t.WhatKind);
        summaries.Append("</td>");
        summaries.Append("<td>");
        if (ShouldMakeSeparatePage(t)) {
          summaries.Append(Link(t.FullDafnyName, Bold(t.Name)));
        } else if (t is ClassDecl || t is TraitDecl) {
          summaries.Append(Bold(t.Name) + "{}\n");
        } else {
          summaries.Append(Bold(t.Name));
        }
        if (!String.IsNullOrEmpty(docstring)) {
          summaries.Append(Mdash);
          summaries.Append(Shorten(docstring));
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
        var docstring = Docstring(c);
        var modifiers = Modifiers(c);
        var attributes = Attributes(c.Attributes);
        summaries.Append(LinkToAnchor(c.Name, Bold(c.Name))).Append(": ").Append(TypeLink(c.Type));

        if (!String.IsNullOrEmpty(docstring)) {
          summaries.Append(Mdash).Append(ShortAndMore(c, c.Name));
        }
        summaries.Append(br).Append(eol);

        details.Append(Anchor(c.Name)).Append(eol);
        details.Append(RuleWithText(c.Name)).Append(eol);
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
        details.Append(FullDocString(docstring));
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
        var doc = ShortDocstring(c);

        summaries.Append(Row(LinkToAnchor(c.Name, Bold(c.Name)), ":", TypeLink(c.Type), Mdash, doc)).Append(eol);

        var attrs = Attributes(c.Attributes);
        doc = Docstring(c);
        details.Append(Anchor(c.Name)).Append(eol);
        details.Append(RuleWithText(c.Name)).Append(eol);
        if (!String.IsNullOrEmpty(modifiers)) {
          details.Append(modifiers).Append(br).Append(eol);
        }
        details.Append(Bold(c.Name)).Append(": ").Append(TypeLink(c.Type)).Append(br).Append(eol);
        if (!String.IsNullOrEmpty(attrs)) {
          details.Append(space4).Append(attrs).Append(br).Append(eol);
        }
        details.Append(FullDocString(doc));
      }
      summaries.Append(EndTable()).Append(eol);
      summaries.Append(br).Append(eol);
    }
  }

  public void WriteFunctions(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var functions = decl.Members.Where(m => m is Function).Select(m => m as MemberDecl).ToList();
    functions.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (functions.Count > 0) {
      summaries.Append(Heading3("Functions")).Append(eol);
      details.Append(Heading3("Functions")).Append(eol);
      WriteMethodsList(functions, decl, summaries, details);
    }
  }

  public void WriteMethods(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var methods = decl.Members.Where(m => m is Method && !(m as Method).IsLemmaLike).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      summaries.Append(Heading3("Methods")).Append(eol);
      details.Append(Heading3("Methods")).Append(eol);
      WriteMethodsList(methods, decl, summaries, details);
    }
  }

  public void WriteConstructors(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var methods = decl.Members.Where(m => m is Constructor).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      summaries.Append(Heading3("Constructors")).Append(eol);
      details.Append(Heading3("Constructors")).Append(eol);
      WriteMethodsList(methods, decl, summaries, details);
    }
  }

  string MethodSig(MemberDecl m) {
    if (m is Method) {
      var mth = m as Method;
      var typeparams = TypeArgs(mth.TypeArgs);
      var formals = String.Join(", ", mth.Ins.Select(f => TypeString(f)));
      var outformals = String.Join(", ", mth.Outs.Select(f => TypeString(f)));
      if (outformals.Length != 0) outformals = " returns (" + outformals + ")";
      return Bold(m.Name) + typeparams + "(" + formals + ")" + outformals;
    } else if (m is Function) {
      var f = m as Function;
      var typeparams = TypeArgs(f.TypeArgs);
      var formals = String.Join(", ", f.Formals.Select(ff => TypeString(ff)));
      return Bold(m.Name) + typeparams + "(" + formals + "): " + TypeLink(f.ResultType);
    } else {
      return "";
    }
  }

  string TypeString(Formal ff) { // TODO - need modifiers
    return ff.Name + ": " + TypeLink(ff.Type);
  }

  // For methods, lemmas, functions
  public void WriteMethodsList(List<MemberDecl> members, TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    foreach (var m in members) {
      var md = m as IHasDocstring;
      var ms = MethodSig(m);
      AddToIndex(m.Name, decl.FullDafnyName, m.WhatKind);
      var docstring = Docstring(md);
      var modifiers = Modifiers(m);
      var attributes = Attributes(m.Attributes);
      var name = m.Name;
      if (m is Constructor) {
        if (name == "_ctor") {
          name = decl.Name;
        } else {
          name = decl.Name + "." + m.Name;
        }
      }

      String link = $"<a href=\"#{name}\">{name}</a>";
      String mss = ms.ToString().ReplaceFirst(m.Name, link);

      summaries.Append(mss);
      if (!String.IsNullOrEmpty(docstring)) {
        summaries.Append(space4).Append(Mdash).Append(ShortAndMore(md, name));
      }
      summaries.Append(br).Append(eol);

      details.Append(Anchor(name)).Append(eol);
      details.Append(RuleWithText(name)).Append(eol);
      if (!String.IsNullOrEmpty(modifiers)) {
        details.Append(modifiers).Append(br).Append(eol);
      }
      details.Append(m.WhatKind).Append(br).Append(eol);
      mss = ms.ToString().ReplaceFirst(m.Name, Bold(name));
      details.Append(mss).Append(br).Append(eol);

      if (!String.IsNullOrEmpty(attributes)) {
        details.Append(space4).Append(attributes).Append(br).Append(eol);
      }
      details.Append(FullDocString(docstring));
      AppendSpecs(details, m);
    }
  }

  public void WriteLemmas(TopLevelDeclWithMembers decl, StringBuilder summaries, StringBuilder details) {
    var methods = decl.Members.Where(m => m is Method && (m as Method).IsLemmaLike).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (methods.Count() > 0) {
      summaries.Append(Heading3("Lemmas")).Append(eol);
      details.Append(Heading3("Lemmas")).Append(eol);
      WriteMethodsList(methods, decl, summaries, details);
    }
  }

  public string FullDocString(string docstring) {
    if (!String.IsNullOrEmpty(docstring)) {
      return indent + docstring + unindent + eol;
    } else {
      return br + eol;
    }
  }

  // returns true iff some specs were appended to the StringBuilder
  public bool AppendSpecs(StringBuilder details, MemberDecl d) {
    bool some = false;
    if (d is Method) {
      var m = d as Method;
      foreach (var req in m.Req) {
        details.Append(space4).Append("<b>requires</b> ").Append(req.E.ToString()).Append(br).Append(eol);
        some = true;
      }
      //foreach (var mod in m.Mod) {
      // TODO details.Append(space4).Append("modifies ").Append(mod.ToString()).Append(br).Append(eol);
      // some = true;
      //}
      foreach (var en in m.Ens) {
        details.Append(space4).Append("<b>ensures</b> ").Append(en.E.ToString()).Append(br).Append(eol);
        some = true;
      }
      if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
        var dec = String.Join(", ", m.Decreases.Expressions.Select(e => e.ToString()));
        details.Append(space4).Append("<b>decreases</b> ").Append(dec).Append(br).Append(eol);
        some = true;
      }
    } else if (d is Function) {
      var m = d as Function;
      foreach (var req in m.Reads) {
        details.Append(space4).Append("<b>reads</b> ").Append(req.E.ToString()).Append(br).Append(eol);
        some = true;
      }
      foreach (var req in m.Req) {
        details.Append(space4).Append("<b>requires</b> ").Append(req.E.ToString()).Append(br).Append(eol);
        some = true;
      }
      foreach (var en in m.Ens) {
        details.Append(space4).Append("<b>ensures</b> ").Append(en.E.ToString()).Append(br).Append(eol);
        some = true;
      }
      if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
        var dec = String.Join(", ", m.Decreases.Expressions.Select(e => e.ToString()));
        details.Append(space4).Append("<b>decreases</b> ").Append(dec).Append(br).Append(eol);
        some = true;
      }
    }
    return some;
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
        if (ds.Length > 0) ds = Mdash + ds;
        file.WriteLine($"<li>Module <a href=\"{name}.html\">{name}</a>" + ds + "</li>");
      }
      file.WriteLine("</ul>");
      file.Write(foot);
      AnnounceFile(filename);
    }
  }

  public static string TypeLink(Type t) {
    if (t is BasicType) {
      return t.ToString();
    } else if (t is CollectionType) {
      var ct = t as CollectionType;
      return ct.CollectionTypeName + TypeActualParameters(ct.TypeArgs);
    } else if (t is UserDefinedType) {
      var tt = (t as UserDefinedType).ResolvedClass;
      if (tt is ClassDecl) {
        return Link(tt.FullDafnyName, t.ToString()); // TODO - need to do links for type args also
      } else if (tt is NonNullTypeDecl) {
        return Link(tt.FullDafnyName, t.ToString()); // TODO - need to do links for type args also
      } else {
        return tt.ToString(); // TODO - needs links for every other kind of type
      }
    } else {
      return t.ToString(); // TODO - needs links for every other kind of type
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

  // Used for declarations that merit their own page (modules, classes, traits, types with members, ...)
  public String ShortAndMoreForDecl(TopLevelDecl d) {
    var docstring = Docstring(d as IHasDocstring);
    var shortstring = Shorten(docstring);
    String result = "";
    if (!String.IsNullOrEmpty(docstring)) {
      result = shortstring;
      if (shortstring != docstring) {
        result += (" <a href=\"#decl-detail\">(more...)</a>");
      }
    }
    return result;
  }

  public String ShortAndMore(IHasDocstring d, String target) {
    var docstring = Docstring(d);
    var shortstring = Shorten(docstring);
    String result = "";
    if (!String.IsNullOrEmpty(docstring)) {
      result = shortstring;
      if (shortstring != docstring) {
        result += $" <a href=\"#{target}\">(more...)</a>";
      }
    }
    return result;
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

  public String RuleWithText(String text) {
    return
$"<div style=\"width: 100%; height: 10px; border-bottom: 1px solid black; text-align: center\"><span style=\"font-size: 20px; background-color: #F3F5F6; padding: 0 10px;\">{text}</span></div><br>";
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

  public static string TypeActualParameters(List<Type> args) {
    if (args.Count == 0) return "";
    return "&lt;" + String.Join(",", args.Select(a => TypeLink(a))) + "&gt;";
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
    file.Write($"<div>\n<h1>Index for Dafny Program: {DafnyProgram.Name}{space4}{Smaller(contentslink)}</h1>\n</div>");
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
      file.WriteLine(Mdash + value + br);
    }
    file.Write(foot);
  }

  static string br = "<br>";

  static string contentslink = "<a href=\"index.html\">[table of contents]</a>";
  static string indexlink = "<a href=\"nameindex.html\">[index]</a>";


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
  background-color: #fefdcc
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

public static partial class Extensions {
  /// <summary>
  ///     A string extension method that replace first occurence.
  /// </summary>
  /// <param name="this">The @this to act on.</param>
  /// <param name="oldValue">The old value.</param>
  /// <param name="newValue">The new value.</param>
  /// <returns>The string with the first occurence of old value replace by new value.</returns>
  public static string ReplaceFirst(this string @this, string oldValue, string newValue) {
    int startindex = @this.IndexOf(oldValue);

    if (startindex == -1) {
      return @this;
    }

    return @this.Remove(startindex, oldValue.Length).Insert(startindex, newValue);
  }

  /// <summary>
  ///     A string extension method that replace first number of occurences.
  /// </summary>
  /// <param name="this">The @this to act on.</param>
  /// <param name="number">Number of.</param>
  /// <param name="oldValue">The old value.</param>
  /// <param name="newValue">The new value.</param>
  /// <returns>The string with the numbers of occurences of old value replace by new value.</returns>
  public static string ReplaceFirst(this string @this, int number, string oldValue, string newValue) {
    List<string> list = @this.Split(oldValue).ToList();
    int old = number + 1;
    IEnumerable<string> listStart = list.Take(old);
    IEnumerable<string> listEnd = list.Skip(old);

    return string.Join(newValue, listStart) +
           (listEnd.Any() ? oldValue : "") +
           string.Join(oldValue, listEnd);
  }
}

