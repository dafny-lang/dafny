using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Text.RegularExpressions;
using System.Text;

using static Microsoft.Dafny.DafnyDocHtml;

namespace Microsoft.Dafny;

/* 
TODO:

- when lengthy content is scrolled down and then short content is displayed, the user has to manually scroll back up. Should
implement some mechanism to always or when needed scroll back up automatically.
- Better way to set the indentation in the sidebar

- translate markdown to html
- mark experimental
- add bodies of non-opaque functions
- use project file

- need to revise so that names that differ only in case do not resolve to the same html file on case-insenstive OSes

Future Improvements:
- identify members from refinement parent; link to them
- add details of abstract import
- import details should distinguish provides and reveals
- retain source layout of expressions
- add Dafny favicon
- ability to link to declarations in other documentation sets

- Check formatting
  - is list of imported names in monospace

Questions
- Should functions show body?
- list known subtypes of traits?
- omit default decreases?
- mark members that override declarations in traits?
*/


class Info {
  public List<Info> Contents = null;
  public string Kind;
  public string Name;
  public string FullName;
  public string Id;
  public string Link;
  public string HtmlSummary;
  public string HtmlDetail;

  public Info(DafnyDoc dd, string kind, string name, string fullname) : this(dd, kind, name, fullname, fullname) {
  }

  public Info(DafnyDoc dd, string kind, string name, string fullname, string id) {
    this.Contents = null;
    this.Kind = kind;
    this.Name = name;
    this.FullName = fullname;
    this.Id = id;
    this.Link = LinkTarget(id);
    dd.Register(this);
  }
}
class DafnyDoc {
  public static DafnyDriver.ExitValue DoDocumenting(IList<DafnyFile> dafnyFiles, List<string> dafnyFolders,
    ErrorReporter reporter, string programName, DafnyOptions options) {

    string outputdir = options.DafnyPrintCompiledFile;
    if (outputdir == null) {
      outputdir = DefaultOutputDir;
    }

    // Collect all the dafny files
    var exitValue = DafnyDriver.ExitValue.SUCCESS;
    dafnyFiles = dafnyFiles.Concat(dafnyFolders.SelectMany(folderPath => {
      return Directory.GetFiles(folderPath, "*.dfy", SearchOption.AllDirectories)
          .Select(name => new DafnyFile(name)).ToList();
    })).ToList();
    Console.Out.Write($"Documenting {dafnyFiles.Count} files from {dafnyFolders.Count} folders\n");
    if (dafnyFiles.Count == 0) {
      return exitValue;
    }

    // TODO - adjust this to handle project files

    // Do parsing and resolution, obtaining a dafnyProgram
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

      // create the output folder if needed
      if (!Directory.Exists(outputdir)) {
        Directory.CreateDirectory(outputdir);
      }

      // Check writable
      try {
        File.Create(outputdir + "/index.html").Dispose();
      } catch (Exception) {
        reporter.Error(MessageSource.Documentation, Token.NoToken, "Insufficient permission to create output files in " + outputdir);
        return DafnyDriver.ExitValue.DAFNY_ERROR;
      }
      // Generate all the documentation
      exitValue = new DafnyDoc(dafnyProgram, reporter, options, outputdir).GenerateDocs(dafnyFiles);
    }
    return exitValue;
  }


  public void Register(Info info) {
    AllInfo.Add(info);
    script.Append(ScriptEntry(info.Id));
  }

  public Program DafnyProgram;
  public ErrorReporter Reporter;
  public DafnyOptions Options;
  public string Outputdir;
  List<Info> AllInfo = new List<Info>();
  public StringBuilder sidebar = new StringBuilder();
  public StringBuilder script = new StringBuilder().Append(ScriptStart());

  public DafnyDoc(Program dafnyProgram, ErrorReporter reporter, DafnyOptions options, string outputdir) {
    this.DafnyProgram = dafnyProgram;
    this.Reporter = reporter;
    this.Options = options;
    this.Outputdir = outputdir;
  }

  public DafnyDriver.ExitValue GenerateDocs(IList<DafnyFile> dafnyFiles) {
    try {
      var modDecls = new List<LiteralModuleDecl>();
      var rootModule = DafnyProgram.DefaultModule;
      var decls = rootModule.ModuleDef.TopLevelDecls.Select(d => !(d is LiteralModuleDecl));
      sidebar.Append(Size(Bold("Declarations"), LocalHeaderSize) + br + eol);
      var info = ModuleInfo(rootModule, dafnyFiles);
      script.Append(ScriptEnd());
      // Call the following to geneate pages after all the Info structures have been generated
      AddSideBarEntry(info, sidebar, true);
      WriteTOC();
      WritePages();
      WriteStyle();
      return DafnyDriver.ExitValue.SUCCESS;
    } catch (Exception e) {
      // This is a fail-safe backstop so that dafny itself does not crash
      Reporter.Error(MessageSource.Documentation, DafnyProgram.DefaultModule, $"Unexpected exception while generating documentation: {e.Message}\n{e.StackTrace}");
      return DafnyDriver.ExitValue.DAFNY_ERROR;
    }
  }

  public int ModuleLevel(string moduleName) {
    return moduleName.Count(c => c == '.');
  }

  public void AddSideBarEntry(Info info, StringBuilder sb, bool open = false) {
    int level = ModuleLevel(info.FullName);
    if (info.Contents != null) {
      var openstring = open ? "open " : "";
      sb.Append($"<details {openstring}style=\"margin-left: {level * 6}px;\"><summary><a id=\"{info.Id}\" href=\"{info.Link}\">{info.Name}</a></summary>\n");
      foreach (var d in info.Contents) {
        AddSideBarEntry(d, sb);
      }
      sb.Append("</details>\n");
    } else {
      // TODO: The settings of Spaces here and margin-left above are meant to (1) create some visible indentation for different
      // levels of nesting the in sidebar and (2) have items without a twistie line up with their openable siblings
      // There likely is a much better and more principled way to do this aligning.
      sb.Append(Spaces(level * 2 + 3) + $"<a id=\"{info.Id}\" href=\"{info.Link}\">{info.Name}</a>");
      sb.Append(br);
      sb.Append(eol);
    }
  }

  public void WritePages() {
    foreach (var info in AllInfo) {
      var filename = Outputdir + "/" + info.Link;
      using StreamWriter file = new(filename);
      file.Write(HtmlStart($"Dafny Documentation{ProgramHeader()}"));
      file.Write(BodyStart());
      file.Write(LocalHeading(info.Kind, info.FullName));
      file.Write(MainStart("full"));
      file.WriteLine(br);
      file.Write(info.HtmlDetail);
      file.WriteLine(MainEnd());
      file.Write(BodyAndHtmlEnd());
      AnnounceFile(filename);
    }
  }

  public static string LocalHeading(String kind, string fullname) {
    return Size(Bold(kind + " " + QualifiedNameWithLinks(fullname, false)), LocalHeaderSize);
  }

  public Info ModuleInfo(LiteralModuleDecl module, IList<DafnyFile> dafnyFiles) {
    var moduleDef = module.ModuleDef;
    var fullName = moduleDef.FullDafnyName;
    var parent = module.EnclosingModuleDefinition;
    if (moduleDef.IsDefaultModule) {
      fullName = RootName;
      parent = null;
    }
    var defaultClass = moduleDef.TopLevelDecls.First(d => d is ClassDecl cd && cd.IsDefaultClass) as ClassDecl;

    var info = new Info(this, "module", moduleDef.IsDefaultModule ? "_" : moduleDef.Name, fullName);
    info.Contents = new List<Info>();

    var docstring = Docstring(module);

    info.HtmlSummary = $"{Keyword("module")} {QualifiedNameWithLinks(module.FullDafnyName)} {DashShortDocstring(module)}";

    var details = new StringBuilder();
    var abs = moduleDef.IsAbstract ? "abstract " : ""; // The only modifier for modules

    string refineText = "";
    if (moduleDef.RefinementQId != null) {
      refineText = (" refines " + QualifiedNameWithLinks(moduleDef.RefinementQId.Decl.FullDafnyName));
    }
    details.Append(BodyStart());
    details.Append(MainStart("full"));

    // TODO - ToString ought to put out a full declaration, as in the source code, so we don't ahve to reconstruct it here
    // but it doesn't
    var decl = module.ToString();
    var pos = decl.IndexOf('{');
    if (pos > 0) {
      decl = decl[0..(pos - 1)];
    }

    details.Append(AttrString(module.Attributes));
    details.Append(Code(abs + "module " + decl + refineText));
    details.Append(br);
    details.Append(br);
    details.Append(eol);

    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(IndentedHtml(docstring));
      details.Append(br);
      details.Append(eol);
    }

    if (moduleDef.IsDefaultModule) {
      if (dafnyFiles == null) {
        // write nothing
      } else if (dafnyFiles.Count != 1) {
        details.Append("From multiple files<br>\n");
      } else {
        details.Append(FileInfo(dafnyFiles[0].CanonicalPath));
      }
    } else {
      details.Append(FileInfo(module.Tok));
    }

    AddExportSummaries(moduleDef, details, info);
    AddImportSummaries(moduleDef, details, info);
    AddSubModuleSummaries(moduleDef, details, info);
    AddTypeSummaries(moduleDef, details, info);
    AddConstantSummaries(defaultClass, details, info.Contents);
    AddFunctionSummaries(defaultClass, details, info.Contents);
    AddMethodSummaries(defaultClass, details, info.Contents);
    AddLemmaSummaries(defaultClass, details, info.Contents);

    details.Append(MainEnd());
    details.Append(BodyAndHtmlEnd());
    info.HtmlDetail = details.ToString();
    return info;
  }


  /** Returns printable info about the file containing the given token and the last modification time of the file */
  public string FileInfo(IToken tok) {
    if (tok != null) {
      return FileInfo(tok.Filename);
    }
    return "";
  }

  public string FileInfo(string filename) {
    string declFilename = GetFileReference(filename);
    if (declFilename != null) {
      var modifyTime = File.GetLastWriteTime(filename);
      var result = $"From file: {declFilename}{br}\n";
      if (Options.Get(DocCommand.DocShowModifyTime)) {
        result += $"Last modified: {modifyTime}{br}\n";
      }
      return result;
    }
    return "";
  }

  /** Massages a filename into the form requested by the --doc-file-name option */
  public string GetFileReference(string absoluteFile) {
    var r = Options.Get(DocCommand.DocFilenameFormat);
    if (r == null || r == "name") {
      return Path.GetFileName(absoluteFile);
    } else if (r == "none") {
      return null;
    } else if (r == "absolute") {
      return absoluteFile;
    } else if (r.StartsWith("relative")) { // Allow either relative: or relative=
      var prefix = r.Substring("relative".Length + 1);
      return Path.GetRelativePath(prefix, absoluteFile);
    } else {
      // Default or unrecognized value
      return Path.GetFileName(absoluteFile);
    }
  }

  // Export ids can have the same names as other identifiers (in particular, modules), so
  // we adjust the id so as not to have conflicts
  public string ExportId(string fullname) {
    return fullname + "__export";
  }

  public Info ExportInfo(ModuleExportDecl ex) {
    var name = ex.Name;
    var docstring = Docstring(ex);
    var info = new Info(this, "export", name, ex.FullDafnyName, ExportId(ex.FullDafnyName));

    info.HtmlSummary = $"{Keyword("export")} {Code(ex.EnclosingModuleDefinition.Name)}`{Link(info.Id, Code(Bold(ex.Name)))}"
     + DashShortDocstring(ex);

    var details = new StringBuilder();
    var text = Code("export " + ex.Name);

    var extends = String.Join(", ", ex.Extends.Select(e => Link(info.Id, Code(e.val))).ToList());
    if (ex.Extends.Count > 0) {
      extends = " " + Keyword("extends") + " " + extends;
    }
    details.Append(text).Append(extends).Append(br).Append(eol);
    var revealed = ex.Exports.Where(e => !e.Opaque).ToList();
    revealed.Sort((e1, e2) => e1.Id.CompareTo(e2.Id));
    var provided = ex.Exports.Where(e => e.Opaque).ToList();
    provided.Sort((e1, e2) => e1.Id.CompareTo(e2.Id));
    details.Append(space4).Append(Keyword("provides"));
    if (ex.ProvideAll) {
      details.Append(" * :");
    }
    foreach (var e in provided) {
      string id = Code(Bold(e.Id));
      var d = e.Decl;
      var fn = d is MemberDecl ? (d as MemberDecl).FullDafnyName : (d as TopLevelDecl).FullDafnyName;
      string link = Link(fn, id);
      details.Append(" ").Append(link);
    }
    details.Append(br).Append(eol);
    details.Append(space4).Append(Keyword("reveals"));
    if (ex.RevealAll) {
      details.Append(" * :");
    }
    foreach (var e in revealed) {
      string id = Code(Bold(e.Id));
      var d = e.Decl;
      var fn = d is MemberDecl ? (d as MemberDecl).FullDafnyName : (d as TopLevelDecl).FullDafnyName;
      string link = Link(fn, id);
      details.Append(" ").Append(link);
    }
    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(IndentedHtml(docstring));
    }
    details.Append(eol);

    info.HtmlDetail = details.ToString();
    return info;
  }

  public void AddExportSummaries(ModuleDefinition module, StringBuilder summaries, Info owner) {

    var exports = module.TopLevelDecls.Where(d => d is ModuleExportDecl).Select(d => d as ModuleExportDecl);
    if (exports.Count() > 0) {
      summaries.Append(Heading3("Export sets")).Append(eol);
      foreach (var ex in exports) {
        var info = ExportInfo(ex);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(br).Append(eol);
      }
    }
  }

  public Info ImportInfo(ModuleDecl md) {
    var name = md.Name;
    var docstring = Docstring(md);
    var info = new Info(this, "import", name, md.FullDafnyName, md.FullDafnyName + "__import");

    var styledName = Code(Bold(name));
    var details = new StringBuilder();
    List<MemberDecl> list = null;
    List<TopLevelDecl> list2 = null;
    if (md is AliasModuleDecl imp) {
      var openText = imp.Opened ? "opened " : "";
      var target = imp.Dereference();
      var exportsets = String.Join(", ", imp.Exports.Select(e => Link(ExportId(target.FullDafnyName + "." + e.val), Code(e.val))));
      if (exportsets.Length == 0) {
        exportsets = Link(ExportId(target.FullDafnyName + "." + target.Name), Code(target.Name));
      }
      info.HtmlSummary = $"import {Link(info.Id, styledName)} = {QualifiedNameWithLinks(target.FullDafnyName)}`{exportsets}"
         + DashShortDocstring(imp);
      details.Append(Code("import " + openText + name + " = " + QualifiedNameWithLinks(target.FullDafnyName) + "`" + exportsets));
      list = imp.AccessibleSignature(true).StaticMembers.Values.ToList();
      list2 = imp.AccessibleSignature(true).TopLevels.Values.Where(d => !(d is ClassDecl && (d as ClassDecl).IsDefaultClass)).ToList();
    } else if (md is AbstractModuleDecl aimp) {
      var openText = aimp.Opened ? "opened " : "";
      var target = aimp.OriginalSignature.ModuleDef.FullDafnyName;
      info.HtmlSummary = $"import {Link(info.Id, styledName)} : {QualifiedNameWithLinks(target)}"
         + DashShortDocstring(aimp);
      details.Append(Code("import " + openText + name + " : " + QualifiedNameWithLinks(target)));
      list = aimp.AccessibleSignature(true).StaticMembers.Values.ToList();
      list2 = aimp.AccessibleSignature(true).TopLevels.Values.Where(d => !(d is ClassDecl && (d as ClassDecl).IsDefaultClass)).ToList();
    }

    details.Append(br).Append(br).Append(eol);
    details.Append("Names imported:");
    list.Sort((a, b) => a.Name.CompareTo(b.Name));
    list.Sort((a, b) => a.Name.CompareTo(b.Name));
    string result = String.Join("", list.Select(d => " " + Link(d.FullDafnyName, d.Name)));
    result += String.Join("", list2.Select(d => " " + Link(d.FullDafnyName, d.Name)));
    details.Append(Code(result)).Append(br).Append(eol);

    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(br).Append(IndentedHtml(docstring));
    }
    info.HtmlDetail = details.ToString();
    return info;
  }

  public void AddImportSummaries(ModuleDefinition module, StringBuilder summaries, Info owner) {
    var imports = module.TopLevelDecls.Where(d => d is AliasModuleDecl).Select(d => d as AliasModuleDecl).ToList();
    imports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    var absimports = module.TopLevelDecls.Where(d => d is AbstractModuleDecl).Select(d => d as AbstractModuleDecl).ToList();
    absimports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (imports.Count() + absimports.Count() > 0) {
      summaries.Append(Heading3("Imports")).Append(eol);
      foreach (var imp in imports) {
        var info = ImportInfo(imp);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(br).Append(eol);
      }
      foreach (var imp in absimports) {
        var info = ImportInfo(imp);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(br).Append(eol);
      }
    }
  }

  public void AddSubModuleSummaries(ModuleDefinition module, StringBuilder summaries, Info info) {
    var submods = module.TopLevelDecls.Where(d => d is LiteralModuleDecl).Select(d => d as LiteralModuleDecl).ToList();
    submods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (submods.Count() > 0) {
      summaries.Append(Heading3("Submodules")).Append(eol);
      foreach (var submod in submods) {
        var subinfo = ModuleInfo(submod, null);
        summaries.Append(subinfo.HtmlSummary).Append(br).Append(eol);
        info.Contents.Add(subinfo);
      }
    }
  }

  public bool IsType(TopLevelDecl t) {
    return (t is RevealableTypeDecl || t is SubsetTypeDecl);
  }

  public void AddTypeSummaries(ModuleDefinition module, StringBuilder summaries, Info owner) {
    var types = module.TopLevelDecls.Where(c => IsType(c) && !IsGeneratedName(c.Name)).ToList();
    types.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (types.Count() > 1 || (types.Count() == 1 && (types[0] is ClassDecl) && !(types[0] as ClassDecl).IsDefaultClass)) {
      summaries.Append(Heading3("Types")).Append(eol);
      summaries.Append(TableStart());
      foreach (var t in types) {
        if ((t is ClassDecl) && (t as ClassDecl).IsDefaultClass) {
          continue;
        }
        var info = TypeInfo(t, module, owner);
        var styledName = Code(Bold(t.Name));
        summaries.Append(Row(t.WhatKind, Link(info.FullName, styledName), DashShortDocstring(t as IHasDocstring))).Append(eol); // TODO - typeparameters?
      }
      summaries.Append(TableEnd());
    }
  }

  public Info ConstantInfo(ConstantField c, TopLevelDeclWithMembers owner) {
    var info = new Info(this, "const", c.Name, c.FullDafnyName);

    var docstring = Docstring(c);
    var modifiers = c.ModifiersAsString();
    var linkedName = Code(Link(c.FullDafnyName, Bold(c.Name)));
    var linkedType = TypeLink(c.Type);
    var rhsstring = c.Rhs == null ? "" : (" := " + c.Rhs.ToString());

    info.HtmlSummary = linkedName + " : " + linkedType + DashShortDocstring(c);

    var details = new StringBuilder();
    details.Append(AttrString(c.Attributes));
    var decl = modifiers + "const " + Bold(c.Name) + ": " + linkedType + rhsstring;
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    return info;
  }

  public Info VarInfo(Field f, TopLevelDeclWithMembers owner) {
    var info = new Info(this, "var", f.Name, f.FullDafnyName);

    var docstring = Docstring(f);
    var linkedName = Code(Link(f.FullDafnyName, Bold(f.Name)));
    var modifiers = f.ModifiersAsString();
    var linkedType = TypeLink(f.Type);

    info.HtmlSummary = linkedName + " : " + linkedType + DashShortDocstring(f); ;

    var details = new StringBuilder();
    var decl = modifiers + "var " + Bold(f.Name) + ": " + linkedType;
    details.Append(AttrString(f.Attributes));
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    return info;
  }

  public Info ExecutableInfo(MemberDecl m, TopLevelDeclWithMembers owner) {
    var name = m.Name;
    if (m is Constructor) {
      if (name == "_ctor") {
        name = owner.Name;
      } else {
        name = owner.Name + "." + m.Name;
      }
    }

    var info = new Info(this, m.WhatKind, name, m.FullDafnyName);

    var md = m as IHasDocstring;
    var docstring = Docstring(md);
    var modifiers = m.ModifiersAsString();
    var ms = MethodSig(m);

    String link = Link(info.FullName, name);
    // Replacing the name with a link -- the angle brackets are to be sure we get the whole name and 
    // not a portion of someother html tag. At this point the name is enclosed in some styling tag.
    String mss = ReplaceFirst(ms, ">" + m.Name + "<", ">" + link + "<");

    var summaries = new StringBuilder();
    var details = new StringBuilder();
    summaries.Append(Code(mss));
    if (!String.IsNullOrEmpty(docstring)) {
      summaries.Append(space4).Append(DashShortDocstring(md));
    }
    summaries.Append(br).Append(eol);

    details.Append(AttrString(m.Attributes));
    var decl = modifiers + m.WhatKind + " " + ms;
    details.Append(Code(decl)).Append(br).Append(eol);

    details.Append(IndentedHtml(docstring));
    AppendSpecs(details, m);

    info.HtmlSummary = summaries.ToString();
    info.HtmlDetail = details.ToString();
    return info;
  }

  public Info TypeInfo(TopLevelDecl t, ModuleDefinition module, Info owner) {
    var link = Link(t.FullDafnyName, Code(Bold(t.Name)));

    var docstring = t is IHasDocstring ? Docstring(t as IHasDocstring) : "";
    // Note: Types do not have modifiers (at least at present)
    var modifiers = "";
    var typeparams = TypeFormals(t.TypeArgs);
    string kind = t.WhatKind.Replace("abstract", "").Replace("opaque", "");

    var info = new Info(this, t.WhatKind, t.Name, t.FullDafnyName);

    var details = new StringBuilder();

    info.HtmlSummary = ($"{Code(kind)} {Code(link + typeparams)} {DashShortDocstring(t as IHasDocstring)}");

    var decl = new StringBuilder();
    decl.Append(modifiers + kind + " " + Bold(t.Name));
    // TODO: Should refactor the Characteristics field into an interface
    if (t is SubsetTypeDecl tsd) {
      decl.Append(tsd.Characteristics.ToString());
    } else if (t is TypeSynonymDecl tsy) {
      decl.Append(tsy.Characteristics.ToString());
    } else if (t is OpaqueTypeDecl atd) {
      decl.Append(atd.Characteristics.ToString());
    }
    decl.Append(typeparams);

    if (t is ClassDecl cd) { // Class, Trait, Iterator
      if (cd.ParentTraits.Count > 0) {
        var extends = String.Join(", ", cd.ParentTraits.Select(t => TypeLink(t)));
        decl.Append(" ").Append(extends);
      }
    } else if (t is SubsetTypeDecl ts) {
      decl.Append(" = ").Append(ts.Var.Name).Append(": ").Append(TypeLink(ts.Var.Type)).Append(" | ").Append(ts.Constraint.ToString());
      if (ts.WitnessKind == SubsetTypeDecl.WKind.OptOut) {
        decl.Append(" witness *");
      } else if (ts.Witness != null) {
        decl.Append(" witness ").Append(ts.Witness.ToString());
      }
    } else if (t is TypeSynonymDecl tsy) {
      decl.Append(" = ").Append(TypeLink(tsy.Rhs));
    } else if (t is NewtypeDecl tnt) {
      if (tnt.Var != null) {
        decl.Append(" = ").Append(tnt.Var.Name).Append(": ").Append(TypeLink(tnt.Var.Type)).Append(" | ").Append(tnt.Constraint.ToString());
      } else {
        decl.Append(" = ").Append(TypeLink(tnt.BaseType));
      }
      if (tnt.WitnessKind == SubsetTypeDecl.WKind.OptOut) {
        decl.Append(" witness *");
      } else if (tnt.Witness != null) {
        decl.Append(" witness ").Append(tnt.Witness.ToString());
      }
    } else if (t is OpaqueTypeDecl otd) {
      // nothing else
    } else if (t is DatatypeDecl) {
      decl.Append(" = ");
      // datatype constructors are written out several lines down
    } else {
      Reporter.Warning(MessageSource.Documentation, null, t.Tok, "Kind of type not handled in dafny doc");
    }
    decl.Append(br).Append(eol);
    details.Append(AttrString(t.Attributes));
    details.Append(Code(decl.ToString()));

    if (t is DatatypeDecl dt) {
      details.Append(TableStart());
      foreach (var ctor in dt.Ctors) {
        string sig = ctor.Name;
        if (ctor.Formals.Count > 0) {
          sig += "(" + String.Join(", ", ctor.Formals.Select(ff => FormalAsString(ff, false))) + ")";
        }
        var cdocstring = Docstring(ctor);
        if (String.IsNullOrEmpty(cdocstring)) {
          details.Append(Row(initialbar, ctor.IsGhost ? Code("ghost") : "", Code(sig), "", ""));
        } else {
          details.Append(Row(initialbar, ctor.IsGhost ? Code("ghost") : "", Code(sig), mdash, ToHtml(cdocstring)));
        }
      }
      details.Append(TableEnd());
    }

    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(IndentedHtml(docstring));
    } else {
      details.Append(br).Append(eol);
    }

    if (t is TopLevelDeclWithMembers tm) {
      info.Contents = tm.Members.Count == 0 ? null : new List<Info>();
      details.Append(FileInfo(tm.Tok));

      if (tm is ClassDecl) {
        AddConstructorSummaries(tm, details, info.Contents);
      }
      AddConstantSummaries(tm, details, info.Contents);
      AddFieldSummaries(tm, details, info.Contents);
      AddFunctionSummaries(tm, details, info.Contents);
      AddMethodSummaries(tm, details, info.Contents);
      AddLemmaSummaries(tm, details, info.Contents);
    }

    owner.Contents.Add(info);
    info.HtmlDetail = details.ToString();
    return info;
  }


  /** Append the summary and detail information about const declarations to the string builders */
  public void AddConstantSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var constants = decl.Members.Where(c => c is ConstantField && !IsGeneratedName(c.Name)).Select(c => c as ConstantField).ToList();
    constants.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (constants.Count() > 0) {
      summaries.Append(Heading3("Constants\n"));
      summaries.Append(TableStart()).Append(eol);
      foreach (var c in constants) {
        var info = ConstantInfo(c, decl);
        ownerInfoList.Add(info);

        var styledName = Code(Bold(c.Name));
        var linkedType = TypeLink(c.Type);

        summaries.Append(Row(Link(info.FullName, styledName), " : ", linkedType, DashShortDocstring(c))).Append(eol);

      }
      summaries.Append(TableEnd()).Append(eol);
    }
  }

  public void AddFieldSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var fields = decl.Members.Where(c => c is Field && c is not ConstantField && !IsGeneratedName(c.Name)).Select(c => c as Field).ToList();
    fields.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (fields.Count() > 0) {
      summaries.Append(Heading3("Mutable Fields\n"));
      summaries.Append(TableStart()).Append(eol);
      foreach (var c in fields) {
        var info = VarInfo(c, decl);
        ownerInfoList.Add(info);

        var linkedType = TypeLink(c.Type);
        var styledName = Code(Bold(c.Name));

        summaries.Append(Row(Link(info.FullName, styledName), " : ", linkedType, DashShortDocstring(c))).Append(eol);
      }
      summaries.Append(TableEnd()).Append(eol);
    }
  }

  public void AddFunctionSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var functions = decl.Members.Where(m => m is Function && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    functions.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Functions", functions, decl, summaries, ownerInfoList);
  }

  public void AddMethodSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var methods = decl.Members.Where(m => m is Method && !(m as Method).IsLemmaLike && !(m is Constructor) && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Methods", methods, decl, summaries, ownerInfoList);
  }

  public void AddLemmaSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var methods = decl.Members.Where(m => m is Method && (m as Method).IsLemmaLike && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Lemmas", methods, decl, summaries, ownerInfoList);
  }

  public void AddConstructorSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var methods = decl.Members.Where(m => m is Constructor && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Constructors", methods, decl, summaries, ownerInfoList);
  }

  string MethodSig(MemberDecl m) {
    if (m is Method) {
      var mth = m as Method;
      var typeparams = TypeFormals(mth.TypeArgs);
      var formals = String.Join(", ", mth.Ins.Select(f => (FormalAsString(f, false))));
      var outformals = mth.Outs.Count == 0 ? "" :
        " " + Keyword("returns") + " (" + String.Join(", ", mth.Outs.Select(f => (FormalAsString(f, false)))) + ")";
      return (Bold(m.Name) + typeparams) + "(" + formals + ")" + outformals;
    } else if (m is Function) {
      var f = m as Function;
      var typeparams = TypeFormals(f.TypeArgs);
      var allowNew = m is TwoStateFunction;
      var formals = String.Join(", ", f.Formals.Select(ff => FormalAsString(ff, allowNew)));
      return (Bold(m.Name) + typeparams) + "(" + formals + "): " + TypeLink(f.ResultType);
    } else {
      return "";
    }
  }

  // A string representation of a formal parameter, but with the type having links to type declarations
  string FormalAsString(Formal ff, bool allowNew) {
    string ss = "";
    if (ff.IsGhost) {
      ss += "ghost ";
    }
    if (ff.IsOlder) {
      ss += "older ";
    }
    if (!ff.IsOld && allowNew) {
      ss += "new ";
    }
    if (ff.IsNameOnly) {
      ss += "nameonly ";
    }
    string def = ff.DefaultValue == null ? "" : " := " + Code(ff.DefaultValue.ToString());
    return (ss == "" ? "" : Keyword(ss)) + Code(ff.Name) + ": " + TypeLink(ff.Type) + def;
  }

  // For methods, lemmas, functions
  public void AddExecutableSummaries(string kind, List<MemberDecl> members, TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    if (members.Count == 0) return;
    summaries.Append(Heading3(kind));
    summaries.Append(TableStart()).Append(eol);
    foreach (var m in members) {
      var info = ExecutableInfo(m, decl);
      ownerInfoList.Add(info);
      summaries.Append(Row(info.HtmlSummary));
    }
    summaries.Append(TableEnd());
  }

  public static string AttrString(Attributes attr) {
    if (attr != null) {
      return Code(space4 + attr.ToString()) + br + eol;
    } else {
      return "";
    }

  }

  public static bool IsGeneratedName(string name) {
    return (name.Length > 1 && name[0] == '_') || name.StartsWith("reveal_");
  }

  public string IndentedHtml(string docstring, bool nothingIfNull = false) {
    if (!String.IsNullOrEmpty(docstring)) {
      return Indent(ToHtml(docstring)) + eol;
    } else if (!nothingIfNull) {
      return br + eol;
    } else {
      return "";
    }
  }

  // returns true iff some specs were appended to the StringBuilder
  public bool AppendSpecs(StringBuilder details, MemberDecl d) {
    bool some = false;
    if (d is Method) {
      var m = d as Method;
      foreach (var req in m.Req) {
        details.Append(space4).Append(Keyword("requires")).Append(" ").Append(Code(req.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      if (m.Mod != null && m.Mod.Expressions.Count > 0) {
        var list = String.Join(", ", m.Mod.Expressions.Select(e => Code(e.OriginalExpression.ToString() + (e.FieldName != null ? "`" + e.FieldName : ""))));
        details.Append(space4).Append(Keyword("modifies")).Append(" ").Append(list).Append(br).Append(eol);
        some = true;
      }
      foreach (var en in m.Ens) {
        details.Append(space4).Append(Keyword("ensures")).Append(" ").Append(Code(en.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
        var dec = String.Join(", ", m.Decreases.Expressions.Select(e => Code(e.ToString())));
        details.Append(space4).Append(Keyword("decreases")).Append(" ").Append(dec).Append(br).Append(eol);
        some = true;
      }
    } else if (d is Function) {
      var m = d as Function;
      if (m.Reads != null && m.Reads.Count > 0) {
        var list = String.Join(", ", m.Reads.Select(e => Code(e.OriginalExpression.ToString() + (e.FieldName != null ? "`" + e.FieldName : ""))));
        details.Append(space4).Append(Keyword("reads")).Append(" ").Append(list).Append(br).Append(eol);
        some = true;
      }
      foreach (var req in m.Req) {
        details.Append(space4).Append(Keyword("requires")).Append(" ").Append(Code(req.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      foreach (var en in m.Ens) {
        details.Append(space4).Append(Keyword("ensures")).Append(" ").Append(Code(en.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      if (m.Decreases != null && m.Decreases.Expressions.Count > 0) {
        var dec = String.Join(", ", m.Decreases.Expressions.Select(e => Code(e.ToString())));
        details.Append(space4).Append(Keyword("decreases")).Append(" ").Append(dec).Append(br).Append(eol);
        some = true;
      }
    }
    return some;
  }

  public void WriteTOC() {
    string filename = Outputdir + "/index.html";
    using StreamWriter file = new(filename);
    file.Write(HtmlStart($"Dafny Documentation{ProgramHeader()}", script.ToString()));

    file.Write(Heading1($"Dafny Documentation{ProgramHeader()}"));
    file.Write(BodyStart());
    file.Write(MainStart());
    file.WriteLine(MainEnd());
    file.Write(SideBar(sidebar.ToString()));
    file.Write(BodyAndHtmlEnd());
    AnnounceFile(filename);
  }


  public void WriteStyle() {
    string filename = Outputdir + "/styles.css";
    using StreamWriter file = new(filename);
    file.WriteLine(Style);
    AnnounceFile(filename);
  }

  public string ProgramHeader() {
    var programName = Options.Get(DocCommand.DocProgramNameOption);
    return programName == null ? "" : (" for " + programName);
  }

  public string TypeLink(Type tin) {
    Type t = tin is TypeProxy ? (tin as TypeProxy).T : tin;

    if (t is BasicType) {
      return Code(t.ToString());
    } else if (t is CollectionType ct) {
      return Code(ct.CollectionTypeName + TypeActualParameters(ct.TypeArgs));
    } else if (t.IsArrowType) {
      var arrow = t.AsArrowType;
      if (t is UserDefinedType udt) {
        var arrowString = ArrowType.IsTotalArrowTypeName(udt.Name) ? ArrowType.TOTAL_ARROW :
                          ArrowType.IsPartialArrowTypeName(udt.Name) ? ArrowType.PARTIAL_ARROW :
                          ArrowType.ANY_ARROW;
        return TypeLinkArrow(arrow.Args, Code(arrowString), arrow.Result);
      } else {
        return TypeLinkArrow(arrow.Args, Code(ArrowType.ANY_ARROW), arrow.Result);
      }
    } else if (t is UserDefinedType udt) {
      var tt = udt.ResolvedClass;
      String s = null;
      if (tt is ClassDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is NonNullTypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is SubsetTypeDecl sst) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is NewtypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is DatatypeDecl) {
        if (BuiltIns.IsTupleTypeName(udt.Name)) {
          s = "(" + TypeActualParameters(t.TypeArgs, false) + ")";
        } else {
          s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
        }
      } else if (tt is TypeParameter) {
        s = tt.Name;
      } else if (tt is OpaqueTypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      }
      if (s != null) {
        return Code(s);
      }
    }
    Reporter.Warning(MessageSource.Documentation, null, t.Tok, "Implementation missing for type " + t.GetType() + " " + t.ToString());
    return Code(t.ToString());
  }

  public string TypeLinkArrow(List<Type> args, string arrow, Type result) {
    return String.Join(", ", args.Select(arg => TypeLink(arg)))
           + " " + arrow + " " + TypeLink(result);
  }

  public string ToHtml(string text) {
    // TODO: Needs full translation to HTML (escaping special characters, tranlating javadoc and markdown)
    return @"<span class=""doctext"">" + text + "</span>";
  }

  /** Fetches the docstring for the given declaration */
  public string Docstring(IHasDocstring d) {
    if (d == null) {
      return null;
    }
    var ds = d.GetDocstring(Options);
    if (ds == null) {
      return String.Empty;
    }
    return ds.Trim();
  }

  /** Fetches the abbreviated docstring for the given declaration */
  public string ShortDocstring(IHasDocstring d) {
    var ds = Docstring(d);
    return Shorten(ds);
  }

  /** If there is a docstring, returns a dash + the abbreviated docstring */
  public string DashShortDocstring(IHasDocstring d) {
    var docstring = Docstring(d);
    if (!String.IsNullOrEmpty(docstring)) {
      return mdash + ToHtml(Shorten(docstring));
    }
    return "";
  }

  /** Abbreviates the docstring */
  // Stop at end of sentence (.) but not at periods in numbers or qualified names
  public string Shorten(string docstring) {
    if (docstring != null) {
      var match = Regex.Match(docstring, "\\.[ \r\n]");
      if (!match.Success) {
        return docstring;
      } else {
        return docstring.Substring(0, match.Index + 1);
      }
    }
    return String.Empty;
  }

  public String ReplaceFirst(string text, string old, string replacement) {
    var k = text.IndexOf(old);
    if (k == -1) {
      return text;
    }
    return text.Substring(0, k) + replacement + text.Substring(k + old.Length);
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
    return Code(output);
  }

  public string TypeFormals(List<TypeParameter> args) {
    return (args.Count == 0) ? "" :
      "&lt;" + String.Join(",", args.Select(a => Code(TypeParameter.VarianceString(a.VarianceSyntax) + a + a.Characteristics))) + "&gt;";
  }

  public string TypeActualParameters(List<Type> args, bool enclose = true) {
    var s = (args.Count == 0) ? "" :
        (enclose ? "&lt;" : "") + String.Join(",", args.Select(a => TypeLink(a))) + (enclose ? "&gt;" : "");
    return s;
  }

  public void AnnounceFile(string filename) {
    if (Options.CompileVerbose) {
      Console.WriteLine("Writing " + filename);
    }
  }

  public static string DefaultOutputDir = "./docs";
  public static readonly string RootName = "_"; // Name of file for root module
}