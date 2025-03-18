using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Diagnostics;
using System.Text.RegularExpressions;
using System.Text;
using System.Threading.Tasks;
using static Microsoft.Dafny.DafnyDocHtml;

namespace Microsoft.Dafny;

class Info {
  public List<Info> Contents = null;
  public string Kind;
  public string Name;
  public string FullName;
  public string Id;
  public string Link;
  public string HtmlSummary; // one-line summary of this declaration (for use in its parent)
  public string HtmlDetail; // display of the summaries of the contents of this declaration

  public string Source; // information on where the entity is declared

  public Info(bool register, DafnyDoc dd, string kind, IOrigin tok, string name, string fullname) : this(register, dd, kind, tok, name, fullname, fullname) {
  }

  public Info(bool register, DafnyDoc dd, string kind, IOrigin tok, string name, string fullname, string id) {
    this.Contents = null;
    this.Kind = kind;
    this.Name = name;
    this.FullName = fullname;
    this.Id = id;
    this.Link = LinkTarget(id);
    if (tok != null) {
      this.Source = dd.FileInfo(tok);
    }
    if (register) {
      dd.Register(this);
    }
  }
}
class DafnyDoc {
  public static async Task<ExitValue> DoDocumenting(DafnyOptions options) {

    var dafnyFolders = options.SourceFolders;
    var (code, dafnyFiles, _) = await SynchronousCliCompilation.GetDafnyFiles(options);
    if (code != 0) {
      return code;
    }
    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);
    string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";

    string outputDir = options.DafnyPrintCompiledFile;
    if (outputDir == null) {
      outputDir = DefaultOutputDir;
    }

    // Collect all the dafny files; dafnyFiles already includes files from a .toml project file
    var exitValue = ExitValue.SUCCESS;
    var folderFiles = dafnyFolders.Select(folderPath =>
      FormatCommand.GetFilesForFolder(options, folderPath)).SelectMany(x => x);
    dafnyFiles = dafnyFiles.Concat(folderFiles).ToList();
    await options.OutputWriter.WriteAsync($"Documenting {dafnyFiles.Count} files from {dafnyFolders.Count} folders\n");
    if (dafnyFiles.Count == 0) {
      return exitValue;
    }

    // Do parsing and resolution, obtaining a dafnyProgram
    string err = null;
    Program dafnyProgram = null;
    try {
      (dafnyProgram, err) = await DafnyMain.ParseCheck(options.Input, dafnyFiles, programName, options);
    } catch (Exception e) {
      err = "Exception while parsing -- please report the error (use --verbose to see the call stack)";
      if (options.Verbose) {
        await options.OutputWriter.WriteLineAsync(e.ToString()).ConfigureAwait(false);
      }
    }
    if (err != null) {
      exitValue = ExitValue.DAFNY_ERROR;
      await options.OutputWriter.WriteLineAsync(err);
    } else {
      Contract.Assert(dafnyProgram != null);

      // create the output folder if needed
      if (!Directory.Exists(outputDir)) {
        Directory.CreateDirectory(outputDir);
      }

      // Check writable
      try {
        await File.Create(outputDir + "/index.html").DisposeAsync();
      } catch (Exception) {
        await options.OutputWriter.WriteLineAsync("Insufficient permission to create output files in " + outputDir);
        return ExitValue.DAFNY_ERROR;
      }
      // Generate all the documentation
      exitValue = new DafnyDoc(dafnyProgram, options, outputDir).GenerateDocs(dafnyFiles);
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
  List<Info> AllInfo = [];
  public StringBuilder sidebar = new StringBuilder();
  public StringBuilder script = new StringBuilder().Append(ScriptStart());

  public DafnyDoc(Program dafnyProgram, DafnyOptions options, string outputdir) {
    this.DafnyProgram = dafnyProgram;
    this.Reporter = dafnyProgram.Reporter;
    this.Options = options;
    this.Outputdir = outputdir;
  }

  public ExitValue GenerateDocs(IReadOnlyList<DafnyFile> dafnyFiles) {
    try {
      var modDecls = new List<LiteralModuleDecl>();
      var rootModule = DafnyProgram.DefaultModule;
      var decls = rootModule.ModuleDef.TopLevelDecls.Select(d => !(d is LiteralModuleDecl));
      sidebar.Append(Size(Bold("Declarations"), LocalHeaderSize) + br + eol);
      var info = ModuleInfo(true, rootModule, rootModule.ModuleDef, dafnyFiles);
      script.Append(ScriptEnd());
      // Call the following to geneate pages after all the Info structures have been generated
      AddSideBarEntry(info, sidebar, true);
      WriteTOC();
      WritePages();
      WriteStyle();
      return ExitValue.SUCCESS;
    } catch (Exception e) {
      // This is a fail-safe backstop so that dafny itself does not crash
      Reporter.Error(MessageSource.Documentation, DafnyProgram.DefaultModule, $"Unexpected exception while generating documentation: {e.Message}\n{e.StackTrace}");
      return ExitValue.DAFNY_ERROR;
    }
  }

  public int ModuleLevel(string moduleName) {
    return moduleName.Count(c => c == '.');
  }

  public void AddSideBarEntry(Info info, StringBuilder sb, bool open = false) {
    int level = ModuleLevel(info.FullName);
    if (info.Contents != null) {
      var openstring = open ? "open " : "";
      sb.Append($"<details {openstring} style=\"margin-left: {level * 6}px;\"><summary><a id=\"{info.Id}\" href=\"{info.Link}\">{info.Name}</a></summary>\n");
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
      if (!String.IsNullOrEmpty(info.Source)) {
        file.WriteLine(br);
        file.Write(info.Source);
      }
      file.WriteLine(br);
      file.Write(info.HtmlDetail);
      file.Write(BodyAndHtmlEnd());
      AnnounceFile(filename);
    }
  }

  public static string LocalHeading(String kind, string fullname) {
    var q = QualifiedNameWithLinks(fullname, false);
    if (kind == "export") {
      int k = q.LastIndexOf('.');
      var a = q.ToCharArray();
      a[k] = '`';
      q = new string(a);
    }
    return Size(Bold(kind + " " + q), LocalHeaderSize);
  }

  public Info ModuleInfo(bool register, LiteralModuleDecl module, ModuleDefinition moduleDef, IReadOnlyList<DafnyFile> dafnyFiles) {
    var fullName = moduleDef.FullDafnyName;
    var parent = moduleDef.EnclosingModule;
    if (moduleDef.IsDefaultModule) {
      fullName = RootName;
      parent = null;
    }
    var defaultClass = moduleDef.TopLevelDecls.First(d => d is DefaultClassDecl cd) as DefaultClassDecl;

    var info = new Info(register, this, "module", module == null ? null : module.Origin, moduleDef.IsDefaultModule ? "_" : moduleDef.Name, fullName);
    info.Contents = [];

    if (moduleDef.IsDefaultModule) {
      if (dafnyFiles == null) {
        // write nothing
      } else if (dafnyFiles.Count != 1) {
        info.Source = $"From multiple files{br}\n";
      } else {
        info.Source = FileInfo(dafnyFiles[0].CanonicalPath);
      }
    } else if (module != null) {
      info.Source = FileInfo(module.Origin);
    }

    var docstring = Docstring(module);

    if (module != null) {
      info.HtmlSummary = Row(Link(module.FullName, module.Name), DashShortDocstring(module));
    }
    var details = new StringBuilder();
    var modifier = moduleDef.ModuleKind switch {
      ModuleKindEnum.Abstract => "abstract ",
      ModuleKindEnum.Replaceable => "replaceable ",
      _ => ""
    };

    string refineText = "";
    if (moduleDef.Implements != null) {
      var kind = moduleDef.Implements.Kind == ImplementationKind.Replacement ? "replaces" : "refines";
      refineText = ($" {kind} {QualifiedNameWithLinks(moduleDef.Implements.Target.Decl.FullDafnyName)}");
    }
    details.Append(MainStart("full"));

    if (module != null) {
      details.Append(AttrString(moduleDef.Attributes));
      details.Append(Code(modifier + "module " + moduleDef.Name + refineText));
      details.Append(br);
      details.Append(eol);
    } else {
      details.Append("<hr>");
      details.Append(Heading2("Effective exported module:"));
    }

    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(IndentedHtml(docstring));
      details.Append(eol);
    }

    AddExportSummaries(moduleDef, details, info, register);
    AddImportSummaries(moduleDef, details, info, register);
    AddSubModuleSummaries(moduleDef, details, info, register);
    AddTypeSummaries(moduleDef, details, info, register);
    AddConstantSummaries(defaultClass, details, info.Contents, register);
    AddFunctionSummaries(defaultClass, details, info.Contents, register);
    AddMethodSummaries(defaultClass, details, info.Contents, register);
    AddLemmaSummaries(defaultClass, details, info.Contents, register);

    details.Append(MainEnd());
    info.HtmlDetail = details.ToString();
    return info;
  }


  /** Returns printable info about the file containing the given token and the last modification time of the file */
  public string FileInfo(IOrigin tok) {
    if (tok != null) {
      return FileInfo(tok.ActualFilename);
    }
    return "";
  }

  public string FileInfo(string filename) {
    string declFilename = GetFileReference(filename);
    if (declFilename != null) {
      var modifyTime = File.GetLastWriteTime(filename);
      var result = $"From file: {declFilename}{br}";
      if (Options.Get(DocCommand.DocShowModifyTime)) {
        result += $"Last modified: {modifyTime}{br}";
      }
      return "<span class=\"from-file\">" + result + "\n</span>";
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

  public Info ExportInfo(ModuleExportDecl ex, bool register) {
    var name = ex.Name;
    var docstring = Docstring(ex);
    var info = new Info(register, this, "export", ex.Origin, name, ex.FullDafnyName, ExportId(ex.FullDafnyName));

    info.HtmlSummary = Row($"{Keyword("export")} {Code(ex.EnclosingModuleDefinition.Name)}`{Link(info.Id, Code(Bold(ex.Name)))}",
     DashShortDocstring(ex));

    var details = new StringBuilder();
    var text = Code("export " + ex.Name);

    var extends = String.Join(", ", ex.Extends.Select(e => Link(info.Id, e.val)).ToList());
    if (ex.Extends.Count > 0) {
      extends = " extends " + extends;
    }
    details.Append(text).Append(Code(extends)).Append(br).Append(eol);
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

    var minfo = ModuleInfo(false, null, ex.EffectiveModule, null);
    details.Append(minfo.HtmlDetail);

    info.HtmlDetail = details.ToString();
    return info;
  }

  public void AddExportSummaries(ModuleDefinition module, StringBuilder summaries, Info owner, bool register) {

    var exports = module.TopLevelDecls.Where(d => d is ModuleExportDecl).Select(d => d as ModuleExportDecl);
    if (exports.Count() > 0) {
      summaries.Append(Heading3("Export sets"));
      summaries.Append(TableStart());
      foreach (var ex in exports) {
        var info = ExportInfo(ex, register);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(eol);
      }
      summaries.Append(TableEnd());
    }
  }

  public Info ImportInfo(ModuleDecl md, bool register) {
    var name = md.Name;
    var docstring = Docstring(md);
    var info = new Info(register, this, "import", md.Origin, name, md.FullDafnyName, md.FullDafnyName + "__import");

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
      info.HtmlSummary = Row($"import {Link(info.Id, styledName)}", " = ", $"{QualifiedNameWithLinks(target.FullDafnyName)}`{exportsets}",
         DashShortDocstring(imp));
      details.Append(Code($"import {openText}{name} = {QualifiedNameWithLinks(target.FullDafnyName)}`{exportsets}"));
      list = imp.AccessibleSignature(true).StaticMembers.Values.ToList();
      list2 = imp.AccessibleSignature(true).TopLevels.Values.Where(d => !(d is DefaultClassDecl)).ToList();
    } else if (md is AbstractModuleDecl aimp) {
      var openText = aimp.Opened ? "opened " : "";
      var target = aimp.OriginalSignature.ModuleDef.FullDafnyName;
      info.HtmlSummary = Row($"import {Link(info.Id, styledName)}", " : ", QualifiedNameWithLinks(target),
         DashShortDocstring(aimp));
      details.Append(Code($"import {openText}{name} : {QualifiedNameWithLinks(target)}"));
      list = aimp.AccessibleSignature(true).StaticMembers.Values.ToList();
      list2 = aimp.AccessibleSignature(true).TopLevels.Values.Where(d => !(d is DefaultClassDecl)).ToList();
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

  public void AddImportSummaries(ModuleDefinition module, StringBuilder summaries, Info owner, bool register) {
    var imports = module.TopLevelDecls.Where(d => d is AliasModuleDecl).Select(d => d as AliasModuleDecl).ToList();
    imports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    var absimports = module.TopLevelDecls.Where(d => d is AbstractModuleDecl).Select(d => d as AbstractModuleDecl).ToList();
    absimports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (imports.Count() + absimports.Count() > 0) {
      summaries.Append(Heading3("Imports"));
      summaries.Append(TableStart());
      foreach (var imp in imports) {
        var info = ImportInfo(imp, register);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(eol);
      }
      foreach (var imp in absimports) {
        var info = ImportInfo(imp, register);
        owner.Contents.Add(info);
        summaries.Append(info.HtmlSummary).Append(eol);
      }
      summaries.Append(TableEnd());
    }
  }

  public void AddSubModuleSummaries(ModuleDefinition module, StringBuilder summaries, Info owner, bool register) {
    var submods = module.TopLevelDecls.Where(d => d is LiteralModuleDecl).Select(d => d as LiteralModuleDecl).ToList();
    submods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (submods.Count() > 0) {
      summaries.Append(Heading3("Submodules"));
      summaries.Append(TableStart());
      foreach (var submod in submods) {
        var info = ModuleInfo(register, submod, submod.ModuleDef, null);
        owner.Contents.Add(info);
        summaries.Append(Row(info.HtmlSummary)).Append(eol);
      }
      summaries.Append(TableEnd());
    }
  }

  public bool IsType(TopLevelDecl t) {
    return (t is RevealableTypeDecl || t is SubsetTypeDecl);
  }

  public void AddTypeSummaries(ModuleDefinition module, StringBuilder summaries, Info owner, bool register) {
    var types = module.TopLevelDecls.Where(c => IsType(c) && !IsGeneratedName(c.Name)).ToList();
    types.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (types.Count() > 1 || (types.Count() == 1 && (types[0] is DefaultClassDecl))) {
      summaries.Append(Heading3("Types"));
      summaries.Append(TableStart());
      foreach (var t in types) {
        if (t is DefaultClassDecl) {
          continue;
        }
        var info = TypeInfo(register, t, module, owner);
        var styledName = Code(Bold(t.Name));
        owner.Contents.Add(info);
        summaries.Append(Row(info.HtmlSummary)).Append(eol);
      }
      summaries.Append(TableEnd());
    }
  }

  public Info ConstantInfo(bool register, ConstantField c) {
    var info = new Info(register, this, "const", c.Origin, c.Name, c.FullDafnyName);

    var docstring = Docstring(c);
    var modifiers = c.ModifiersAsString();
    var linkedName = Code(Link(c.FullDafnyName, Bold(c.Name)));
    var linkedType = TypeLink(c.Type);
    var rhsstring = c.Rhs == null ? "" : $" := {c.Rhs.ToString()}";

    info.HtmlSummary = Row(linkedName, " : ", linkedType, DashShortDocstring(c));
    var details = new StringBuilder();
    details.Append(AttrString(c.Attributes));
    var decl = modifiers + "const " + Bold(c.Name) + ": " + linkedType + rhsstring;
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    return info;
  }

  public Info VarInfo(bool register, Field f) {
    var info = new Info(register, this, "var", f.Origin, f.Name, f.FullDafnyName);

    var docstring = Docstring(f);
    var linkedName = Code(Link(f.FullDafnyName, Bold(f.Name)));
    var modifiers = f.ModifiersAsString();
    var linkedType = TypeLink(f.Type);

    info.HtmlSummary = Row(linkedName, " : ", linkedType, DashShortDocstring(f));

    var details = new StringBuilder();
    var decl = modifiers + "var " + Bold(f.Name) + ": " + linkedType;
    details.Append(AttrString(f.Attributes));
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    return info;
  }

  public Info ExecutableInfo(bool register, MemberDecl m, TopLevelDeclWithMembers owner) {
    var name = m.Name;
    if (m is Constructor) {
      if (name == "_ctor") {
        name = owner.Name;
      } else {
        name = owner.Name + "." + m.Name;
      }
    }

    var info = new Info(register, this, m.WhatKind, m.Origin, name, m.FullDafnyName);

    var md = m as IHasDocstring;
    var docstring = Docstring(md);
    var modifiers = m.ModifiersAsString();
    var ms = MethodSig(m);

    String link = Link(info.FullName, name);
    // Replacing the name with a link -- the angle brackets are to be sure we get the whole name and 
    // not a portion of someother html tag. At this point the name is enclosed in some styling tag.
    String mss = ReplaceFirst(ms, ">" + m.Name + "<", ">" + link + "<");

    info.HtmlSummary = Row(Code(mss), !String.IsNullOrEmpty(docstring) ? DashShortDocstring(md) : "");

    var details = new StringBuilder();
    details.Append(AttrString(m.Attributes));
    var decl = modifiers + m.WhatKind + " " + ms;
    details.Append(Code(decl)).Append(br).Append(eol);
    AppendSpecs(details, m);
    if (m is Function f) {
      Expression body = f.Body;
      if (body != null) {
        if (f.IsOpaque) {
          details.Append(br).Append(space4).Append("Function body is opaque").Append(br).Append(eol);
        }
        var brackets = new TokenRange(body.StartToken.Prev!, body.EndToken.Next);
        int column = brackets.StartToken.line != brackets.EndToken.line ? brackets.EndToken.col : 0;
        var offset = column <= 1 ? "" : new StringBuilder().Insert(0, " ", column - 1).ToString();
        details.Append(Pre(offset + brackets.PrintOriginal()));
      }
    }

    details.Append(IndentedHtml(docstring));

    info.HtmlDetail = details.ToString();
    return info;
  }

  public string ExpressionAsSource(Expression e) {
    return e.EntireRange.PrintOriginal();
  }

  public Info TypeInfo(bool register, TopLevelDecl t, ModuleDefinition module, Info owner) {
    var link = Link(t.FullDafnyName, Code(Bold(t.Name)));

    var docstring = t is IHasDocstring ? Docstring(t as IHasDocstring) : "";
    // Note: Types do not have modifiers (at least at present)
    var modifiers = "";
    var typeparams = TypeFormals(t.TypeArgs);
    string kind = t.WhatKind.Replace("abstract ", "").Replace("opaque ", "").Replace("subset ", "").Replace(" synonym", "");

    var info = new Info(register, this, t.WhatKind, t.Origin, t.Name, t.FullDafnyName);

    var details = new StringBuilder();

    info.HtmlSummary = Row($"{Code(kind)} {Code(link + typeparams)}", $"{DashShortDocstring(t as IHasDocstring)}");

    var decl = new StringBuilder();
    decl.Append(modifiers + kind + " " + Bold(t.Name));
    // TODO: Should refactor the Characteristics field into an interface
    if (t is SubsetTypeDecl tsd) {
      decl.Append(tsd.Characteristics.ToString());
    } else if (t is TypeSynonymDecl tsy) {
      decl.Append(tsy.Characteristics.ToString());
    } else if (t is AbstractTypeDecl atd) {
      decl.Append(atd.Characteristics.ToString());
    }
    decl.Append(typeparams);

    if (t is ClassLikeDecl cd) { // Class, Trait, Iterator
      if (cd.Traits.Count > 0) {
        var extends = String.Join(", ", cd.Traits.Select(t => TypeLink(t)));
        if (!String.IsNullOrEmpty(extends)) {
          decl.Append(" ").Append("extends").Append(" ").Append(extends);
        }
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
    } else if (t is AbstractTypeDecl otd) {
      // nothing else
    } else if (t is DatatypeDecl) {
      decl.Append(" = ");
      // datatype constructors are written out several lines down
    } else {
      Reporter.Warning(MessageSource.Documentation, ParseErrors.ErrorId.none, t.Origin, "Kind of type not handled in dafny doc");
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
      info.Contents = tm.Members.Count == 0 ? null : [];

      if (tm is ClassDecl) {
        AddConstructorSummaries(tm, details, info.Contents, register);
      }
      AddConstantSummaries(tm, details, info.Contents, register);
      AddFieldSummaries(tm, details, info.Contents, register);
      AddFunctionSummaries(tm, details, info.Contents, register);
      AddMethodSummaries(tm, details, info.Contents, register);
      AddLemmaSummaries(tm, details, info.Contents, register);
    }

    info.HtmlDetail = details.ToString();
    return info;
  }


  /** Append the summary and detail information about const declarations to the string builders */
  public void AddConstantSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var constants = decl.Members.Where(c => c is ConstantField && !IsGeneratedName(c.Name)).Select(c => c as ConstantField).ToList();
    constants.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (constants.Count() > 0) {
      summaries.Append(Heading3("Constants"));
      summaries.Append(TableStart());
      foreach (var c in constants) {
        var info = ConstantInfo(register, c);
        ownerInfoList.Add(info);
        summaries.Append(info.HtmlSummary).Append(eol);
      }
      summaries.Append(TableEnd()).Append(eol);
    }
  }

  public void AddFieldSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var fields = decl.Members.Where(c => c is Field && c is not ConstantField && !IsGeneratedName(c.Name)).Select(c => c as Field).ToList();
    fields.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (fields.Count() > 0) {
      summaries.Append(Heading3("Mutable Fields"));
      summaries.Append(TableStart());
      foreach (var c in fields) {
        var info = VarInfo(register, c);
        summaries.Append(info.HtmlSummary).Append(eol);
        ownerInfoList.Add(info);
      }
      summaries.Append(TableEnd()).Append(eol);
    }
  }

  public void AddFunctionSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var functions = decl.Members.Where(m => m is Function && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    functions.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Functions", functions, decl, summaries, ownerInfoList, register);
  }

  public void AddMethodSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var methods = decl.Members.Where(m => m is Method method && !method.IsLemmaLike && !IsGeneratedName(method.Name)).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Methods", methods, decl, summaries, ownerInfoList, register);
  }

  public void AddLemmaSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var methods = decl.Members.Where(m => m is Method && (m as Method).IsLemmaLike && !IsGeneratedName(m.Name)).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Lemmas", methods, decl, summaries, ownerInfoList, register);
  }

  public void AddConstructorSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    var methods = decl.Members.Where(m => m is Constructor && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Constructors", methods, decl, summaries, ownerInfoList, register);
  }

  string MethodSig(MemberDecl m) {
    if (m is MethodOrConstructor methodOrConstructor) {
      var typeparams = TypeFormals(methodOrConstructor.TypeArgs);
      var formals = String.Join(", ", methodOrConstructor.Ins.Select(f => (FormalAsString(f, false))));
      var outformals = methodOrConstructor.Outs.Count == 0 ? "" :
        " " + Keyword("returns") + " (" + String.Join(", ", methodOrConstructor.Outs.Select(f => (FormalAsString(f, false)))) + ")";
      return (Bold(methodOrConstructor.Name) + typeparams) + "(" + formals + ")" + outformals;
    } else if (m is Function) {
      var f = m as Function;
      var typeparams = TypeFormals(f.TypeArgs);
      var allowNew = m is TwoStateFunction;
      var formals = String.Join(", ", f.Ins.Select(ff => FormalAsString(ff, allowNew)));
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
  public void AddExecutableSummaries(string kind, List<MemberDecl> members, TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList, bool register) {
    if (members.Count != 0) {
      summaries.Append(Heading3(kind));
      summaries.Append(TableStart());
      foreach (var m in members) {
        var info = ExecutableInfo(register, m, decl);
        ownerInfoList.Add(info);
        summaries.Append(Row(info.HtmlSummary)).Append(eol);
      }
      summaries.Append(TableEnd());
    }
  }

  public static string AttrString(Attributes attr) {
    if (attr != null) {
      return Code(attr.ToString()) + br + eol;
    } else {
      return "";
    }

  }

  public static bool IsGeneratedName(string name) {
    return (name.Length > 1 && name[0] == '_') || name.StartsWith(HideRevealStmt.RevealLemmaPrefix);
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
    if (d is MethodOrConstructor method) {
      foreach (var req in method.Req) {
        details.Append(space4).Append(Keyword("requires")).Append(" ").Append(Code(req.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      if (method.Reads.Expressions.Count > 0) {
        var list = String.Join(", ", method.Reads.Expressions.Select(e => Code(e.OriginalExpression.ToString() + (e.FieldName != null ? "`" + e.FieldName : ""))));
        details.Append(space4).Append(Keyword("reads")).Append(" ").Append(list).Append(br).Append(eol);
        some = true;
      }
      if (method.Mod != null && method.Mod.Expressions.Count > 0) {
        var list = String.Join(", ", method.Mod.Expressions.Select(e => Code(e.OriginalExpression.ToString() + (e.FieldName != null ? "`" + e.FieldName : ""))));
        details.Append(space4).Append(Keyword("modifies")).Append(" ").Append(list).Append(br).Append(eol);
        some = true;
      }
      foreach (var en in method.Ens) {
        details.Append(space4).Append(Keyword("ensures")).Append(" ").Append(Code(en.E.ToString())).Append(br).Append(eol);
        some = true;
      }
      if (method.Decreases != null && method.Decreases.Expressions.Count > 0) {
        var dec = String.Join(", ", method.Decreases.Expressions.Select(e => Code(e.ToString())));
        details.Append(space4).Append(Keyword("decreases")).Append(" ").Append(dec).Append(br).Append(eol);
        some = true;
      }
    } else if (d is Function) {
      var m = d as Function;
      if (m.Reads != null && m.Reads.Expressions.Count > 0) {
        var list = String.Join(", ", m.Reads.Expressions.Select(e => Code(e.OriginalExpression.ToString() + (e.FieldName != null ? "`" + e.FieldName : ""))));
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
      if (tt is ClassLikeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is NonNullTypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is SubsetTypeDecl sst) {
        if (tt.FullDafnyName == "nat") {
          s = tt.FullDafnyName;
        } else {
          s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
        }
      } else if (tt is NewtypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is DatatypeDecl) {
        if (SystemModuleManager.IsTupleTypeName(udt.Name)) {
          s = "(" + TypeActualParameters(t.TypeArgs, false) + ")";
        } else {
          s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
        }
      } else if (tt is TypeParameter) {
        s = tt.Name;
      } else if (tt is AbstractTypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else if (tt is TypeSynonymDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      }
      if (s != null) {
        return Code(s);
      }
    }
    Reporter.Warning(MessageSource.Documentation, ParseErrors.ErrorId.none, t.Origin, "Implementation missing for type " + t.GetType() + " " + t.ToString());
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
    if (Options.Verbose) {
      Options.OutputWriter.WriteLine("Writing " + filename);
    }
  }

  public static string DefaultOutputDir = "./docs";
  public static readonly string RootName = "_"; // Name of file for root module
}
