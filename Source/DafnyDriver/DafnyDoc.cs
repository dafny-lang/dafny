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

- when lengthy content is crolled down and then short content is displayed, the user has to manually scroll back up. Should
implement some mechanism to always or when needed scroll back up automatically.
- Better way to set the indentation in the sidebar

- translate markdown to html
- mark experimental
- sidebar - compare to other documentation -- TOC or contents of modules or contents of file -- perhaps openable
- add bodies of non-opaque functions
- use project file
- 

Future Improvements:
- identify members from refinement parent; link to them
- add details of abstract import
- import details should distinguish provides and reveals
- retain source layout of expressions
- make a separate css file
- add Dafny favicon
- ability to link to declarations in other documentation sets
- possibly refactor to combine WriteModule and WriteDecl

- Check formatting
  - is list of imported names in monospace

Questions
- option to maintain source ordering?
- have some options available as module scoped options?
- Should functions show body?
- use table for nameindex?
- add in a cross reference listing?
- list known subtypes of traits?
- omit default decreases?
- use a table for all summary entries?
- modifiers (e.g. ghost) in summary entries?
- overall visual design?
- keep the separation into summary and details?
- improvement to program name title?
- make ghost things italics?
- mark members that override declarations in traits?
- should documentation show declared or inferred/resolved variance and type characterisstics?
- ok to have duplicate index entries for declarations with their own pages?
- should export set names be listed with imported names?
*/

class Info {
  public List<Info> Contents = null;
  public string Kind;
  public string Name;
  public string FullName;
  public string Link;
  public string RawShortDoc;
  public string RawLongDoc;
  public string HtmlSummary;
  public string HtmlDetail;

}

class DafnyDoc {

  Dictionary<string, Info> AllInfo = new Dictionary<string, Info>();

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

  public StringBuilder sidebar = new StringBuilder();

  public StringBuilder script = new StringBuilder().Append(ScriptStart());

  public int ModuleLevel(string moduleName) {
    return moduleName.Count(c => c == '.');
  }

  public void AddSideBarEntry(Info info, StringBuilder sb, bool open = false) {
    int level = ModuleLevel(info.FullName);
    if (info.Contents != null) {
      var openstring = open ? "open " : "";
      sb.Append($"<details {openstring}style=\"margin-left: {level * 6}px;\"><summary><a id=\"{info.FullName}\" href=\"{info.Link}\">{info.Name}</a></summary>\n");
      foreach (var d in info.Contents) {
        AddSideBarEntry(d, sb);
      }
      sb.Append("</details>\n");
    } else {
      // TODO: The settings o Spaces here and margin-left above are meant to (1) ccreate some visible indentation for different
      // levels of nesting the in sidebar and (2) have items without a twistie line up with their openable siblings
      // There likely is a much better and more principled way to do this aligning.
      sb.Append(Spaces(level * 2 + 3) + $"<a id=\"{info.FullName}\" href=\"{info.Link}\">{info.Name}</a>");
      sb.Append(br);
      sb.Append("\n");
    }
  }

  public DafnyDriver.ExitValue GenerateDocs(IList<DafnyFile> dafnyFiles) {
    try {
      var modDecls = new List<LiteralModuleDecl>();
      var rootModule = DafnyProgram.DefaultModule;
      var decls = rootModule.ModuleDef.TopLevelDecls.Select(d => !(d is LiteralModuleDecl));
      sidebar.Append(Size(Bold("Declarations"), LocalHeaderSize) + br + "\n" + Smaller(indexlink) + br + br + "\n");
      var info = ModuleInfo(rootModule, dafnyFiles);
      AddSideBarEntry(info, sidebar, true);
      WriteTOC(modDecls);
      WritePages();
      WriteIndex();
      WriteStyle();
      return DafnyDriver.ExitValue.SUCCESS;
    } catch (Exception e) {
      // This is a fail-safe backstop so that dafny itself does not crash
      Reporter.Error(MessageSource.Documentation, DafnyProgram.DefaultModule, $"Unexpected exception while generating documentation: {e.Message}\n{e.StackTrace}");
      return DafnyDriver.ExitValue.DAFNY_ERROR;
    }
  }

  public void WritePages() {
    for (int i = 0; i < AllInfo.Count; i++) {
      var info = AllInfo.ElementAt(i).Value;
      var filename = Outputdir + "/" + info.Link;
      using StreamWriter file = new(filename);
      file.Write(HtmlStart($"Dafny Documentation{ProgramHeader()}"));

      file.Write(BodyStart());
      file.Write(LocalHeading(info.Kind, info.FullName));
      file.Write(MainStart("full"));
      file.WriteLine(br);
      file.Write(info.HtmlDetail);
      file.WriteLine(MainEnd());
      //file.Write(SideBar(sidebar));
      file.Write(BodyAndHtmlEnd());
      AnnounceFile(filename);
    }
  }

  /** Writes a doc page for the given module */
  public Info WriteModule(LiteralModuleDecl module, IList<DafnyFile> dafnyFiles) {

    var moduleDef = module.ModuleDef;
    var fullName = moduleDef.FullDafnyName;
    var fullNLName = fullName;
    var parent = module.EnclosingModuleDefinition;
    if (moduleDef.IsDefaultModule) {
      nameIndex.Add(RootName + " " + nameIndex.Count + " " + RootName, "module " + Link(RootName, RootName));
      fullName = RootName;
      parent = null;
    } else {
      AddToIndexF(module.Name, fullName, "module");
    }
    var defaultClass = moduleDef.TopLevelDecls.First(d => d is ClassDecl cd && cd.IsDefaultClass) as ClassDecl;

    var info = new Info();
    info.Contents = new List<Info>();
    info.Kind = "module";
    info.Name = moduleDef.IsDefaultModule ? "_" : moduleDef.Name;
    info.FullName = fullName;
    info.Link = LinkTarget(fullName);

    var docstring = Docstring(module);
    info.RawLongDoc = docstring;
    info.RawShortDoc = Shorten(docstring);
    AllInfo.Add(fullNLName, info);

    return info;
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

    var info = new Info();
    info.Contents = new List<Info>();
    info.Kind = "module";
    info.Name = moduleDef.IsDefaultModule ? "_" : moduleDef.Name;
    info.FullName = fullName;
    info.Link = LinkTarget(fullName);

    var docstring = Docstring(module);
    info.RawLongDoc = docstring;
    info.RawShortDoc = Shorten(docstring);
    AllInfo.Add(fullName, info);

    info.HtmlSummary = $"{Keyword("module")} {QualifiedNameWithLinks(module.FullDafnyName)} {DashShortDocstring(module)}";

    var details = new StringBuilder();
    //details.Append(HtmlStart($"Module {fullName} in program {DafnyProgram.Name}"));
    var abs = moduleDef.IsAbstract ? "abstract " : ""; // The only modifier for modules

    string refineText = "";
    if (moduleDef.RefinementQId != null) {
      refineText = (" refines " + QualifiedNameWithLinks(moduleDef.RefinementQId.Decl.FullDafnyName));
    }
    //details.Append(Heading1($"{abs}module {QualifiedNameWithLinks(fullNLName, false)}{space4}"));
    //details.Append(eol);
    details.Append(BodyStart());
    details.Append(MainStart("full"));

    // TODO - ToString ought to put out a full declaration, as in the source code, so we don't ahve to reconstruct it here
    // but it doesn't
    var decl = module.ToString();
    var pos = decl.IndexOf('{');
    if (pos > 0) {
      decl = decl[0..(pos - 1)];
    }

    details.Append(Code(abs + "module " + decl + refineText));
    details.Append(br);
    details.Append(br);
    details.Append(eol);

    if (!String.IsNullOrEmpty(docstring)) {
      details.Append(IndentedHtml(docstring));
      details.Append(br);
      details.Append(eol);
    }
    var attributes = module.Attributes?.ToString();
    if (!String.IsNullOrEmpty(attributes)) {
      details.Append("Attributes: ").Append(Code(attributes)).Append(br).Append(eol);
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

    //StringBuilder summaries = new StringBuilder(1000); // 1000 is arbitrary; defalt of 16 seems unnecessariloy low
    StringBuilder _details = new StringBuilder(1000);
    WriteExports(moduleDef, details, _details);
    WriteImports(moduleDef, details, _details);
    WriteSubModules(moduleDef, details, _details, info);
    AddTypeSummaries(moduleDef, details, info);
    AddConstantSummaries(defaultClass, details, info.Contents);
    AddFunctionSummaries(defaultClass, details, info.Contents);
    AddMethodSummaries(defaultClass, details, info.Contents);
    AddLemmaSummaries(defaultClass, details, info.Contents);

    details.Append(MainEnd());
    details.Append(BodyAndHtmlEnd());
    info.HtmlDetail = details.ToString();
    script.Append(ScriptEntry(info.FullName));
    return info;
  }

  // public Info DeclInfo(TopLevelDeclWithMembers decl, List<Info> ownersList) {
  //   var info = new Info();
  //   info.Kind = decl.WhatKind;
  //   info.Name = decl.Name;
  //   info.FullName = fullName;
  //   info.Link = LinkTarget(fullName);
  //   var docstring = Docstring(decl as IHasDocstring);
  //   info.RawLongDoc = docstring;
  //   info.RawShortDoc = Shorten(docstring);
  //   info.Contents = decl.Members.Count == 0 ? null : new List<Info>();
  //   ownersList.Add(info);
  //   AllInfo.Add(fullName, info);
  //   script.Append(ScriptEntry(info.FullName));

  //   info.HtmlSummary = info.Kind + " " + decl.Name + DashShortDocstring(decl);

  //   var extends = String.Join(", ", decl.ParentTraits.Select(t => TypeLink(t)));
  //   var typeparams = TypeFormals(decl.TypeArgs);

  //   var declaration = info.Kind + " " + info.Name + typeparams;
  //   if (!String.IsNullOrEmpty(extends)) {
  //     declaration += " " + extends;
  //   }
  //   var details = new StringBuilder();
  //   details.Append(Code(declaration)).Append(br).Append(eol);
  //   var attributes = decl.Attributes?.ToString();
  //   if (!String.IsNullOrEmpty(attributes)) {
  //     details.Append("Attributes: ").Append(Code(attributes)).Append(br).Append(eol);
  //   }

  //   if (!String.IsNullOrEmpty(docstring)) {
  //     details.Append(ToHtml(docstring));
  //     details.Append(br).Append(br).Append(eol);
  //   }

  //   details.Append(FileInfo(decl.Tok));

  //   if (decl is ClassDecl) {
  //     AddConstructorSummaries(decl, details, info.Contents);
  //   }
  //   AddConstantSummaries(decl, details, info.Contents);
  //   AddFieldSummaries(decl, details, info.Contents);
  //   AddFunctionSummaries(decl, details, info.Contents);
  //   AddMethodSummaries(decl, details, info.Contents);
  //   AddLemmaSummaries(decl, details, info.Contents);

  //   // TODO: add summaries for inherited members in teh correct section
  //   // if (decl is ClassDecl cd && cd.InheritedMembers.Count > 0) {
  //   //   var sb = new StringBuilder();
  //   //   foreach (var member in cd.InheritedMembers) {
  //   //     var link = QualifiedNameWithLinks(member.EnclosingClass.FullDafnyName, Bold(member.Name));
  //   //     sb.Append(Row(member.WhatKind, link));
  //   //   }
  //   //   var ss = sb.ToString();
  //   //   if (ss != "") {
  //   //     summaries.Append(Heading3("Inherited Members")).Append(eol);
  //   //     summaries.Append(TableStart()).Append(ss).Append(TableEnd());
  //   //   }
  //   // }

  //   info.HtmlDetail = details.ToString();
  //   script.Append(ScriptEntry(info.FullName));
  //   return info;
  // }

  /** Writes files for classes and traits */
  // public void AddDeclSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownersList) {
  //   var info = DeclInfo(decl, ownersList);
  //   AddToIndexF(decl.Name, decl.FullDafnyName, decl.WhatKind);


  //   StringBuilder summaries = new StringBuilder(1000);


  // }

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

  /** Append the summary and detail information about exports to the string builders */
  public void WriteExports(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {

    var exports = module.TopLevelDecls.Where(d => d is ModuleExportDecl).Select(d => d as ModuleExportDecl);
    if (exports.Count() > 0) {
      summaries.Append(Heading3("Export sets")).Append(eol);
      details.Append(Heading3("Export sets")).Append(eol);
      foreach (var ex in exports) {
        AddToIndex(ex.Name, module.FullDafnyName, "export set");
        var text = $"{Keyword("export")} {Code(module.Name)}`{LinkToAnchor(ExportSetAnchor(ex.Name), Code(Bold(ex.Name)))}";
        summaries.Append(text).Append(DashShortDocstring(ex)).Append(br).Append(eol);

        details.Append(Anchor(ExportSetAnchor(ex.Name))).Append(eol);
        details.Append(RuleWithText(ex.Name)).Append(eol);
        var extends = String.Join(", ", ex.Extends.Select(e => LinkToAnchor(ExportSetAnchor(e.val), Code(e.val))).ToList());
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
        // foreach (var e in provided) {
        //   string link;
        //   string id = Code(Bold(e.Id));
        //   var fn = (e.Decl as TopLevelDecl).FullDafnyName;
        //   link = Link(fn, id);
        //   details.Append(" ").Append(link);
        // }
        details.Append(br).Append(eol);
        details.Append(space4).Append(Keyword("reveals"));
        if (ex.RevealAll) {
          details.Append(" * :");
        }
        // foreach (var e in revealed) {
        //   string link;
        //   string id = Code(Bold(e.Id));
        //   var fn = (e.Decl as TopLevelDecl).FullDafnyName;
        //   link = Link(fn, id);
        //   details.Append(" ").Append(link);
        // }
        var docstring = Docstring(ex);
        if (!String.IsNullOrEmpty(docstring)) {
          details.Append(IndentedHtml(docstring));
        }
        details.Append(eol);
      }
    }
  }

  /* Export sets are in a different namespace from other declarations in a module, so they
     might have the same name as another declaration. So we mangle an export set slightly
    so that there will be no duplicate anchor names. */
  public string ExportSetAnchor(string name) {
    return name + "+";
  }

  /** Append the summary and detail information about imports to the string builders */
  public void WriteImports(ModuleDefinition module, StringBuilder summaries, StringBuilder details) {
    var imports = module.TopLevelDecls.Where(d => d is AliasModuleDecl).Select(d => d as AliasModuleDecl).ToList();
    imports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    var absimports = module.TopLevelDecls.Where(d => d is AbstractModuleDecl).Select(d => d as AbstractModuleDecl).ToList();
    absimports.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (imports.Count() + absimports.Count() > 0) {
      summaries.Append(Heading3("Imports")).Append(eol);
      details.Append(Heading3("Imports")).Append(eol);
      foreach (var imp in imports) {
        var name = imp.Name;
        var styledName = Code(Bold(name));
        var target = imp.Dereference();
        var exportsets = String.Join(", ", imp.Exports.Select(e => Link(target.FullDafnyName, Code(e.val))));
        if (exportsets.Length == 0) {
          exportsets = Link(target.FullDafnyName, Code(target.Name)); // TODO - needs cleanup
        }
        summaries.Append($"{Keyword("import")} {LinkToAnchor(name, styledName)} = {QualifiedNameWithLinks(target.FullDafnyName)}`{exportsets}").Append(br).Append(eol);

        details.Append(Anchor(name)).Append(eol);
        details.Append(RuleWithText(imp.Name)).Append(eol);
        details.Append("import ").Append(Code(name)).Append(" ").Append(Bold(imp.Opened ? "IS " : "IS NOT ")).Append("opened").Append(br).Append(eol);
        details.Append("Names imported:");
        var list = imp.AccessibleSignature(true).StaticMembers.Values.ToList();
        list.Sort((a, b) => a.Name.CompareTo(b.Name));
        var list2 = imp.AccessibleSignature(true).TopLevels.Values.Where(d => !(d is ClassDecl && (d as ClassDecl).IsDefaultClass)).ToList();
        list.Sort((a, b) => a.Name.CompareTo(b.Name));
        string result = String.Join("", list.Select(d => " " + ImportLink(d)));
        result += String.Join("", list2.Select(d => " " + ImportLink(d)));
        details.Append(Code(result)).Append(br).Append(eol);
      }
      foreach (var imp in absimports) {
        var name = imp.Name;
        var target = imp.OriginalSignature.ModuleDef.FullDafnyName;
        summaries.Append($"import {name} : {QualifiedNameWithLinks(target)}").Append(eol);
      }
    }
  }

  public string ImportLink(MemberDecl d) {  // TODO -- this needs cleanup
    string link;
    link = Link(d.FullDafnyName, d.Name);
    return link;
  }
  public string ImportLink(TopLevelDecl d) {  // TODO -- this needs cleanup
    string link;
    link = Link(d.FullDafnyName, d.Name);
    return link;
  }

  /** Append the summary information about nested module declarations to the string builders;
      the detail information is on a different html page. */
  public void WriteSubModules(ModuleDefinition module, StringBuilder summaries, StringBuilder details, Info info) {
    var submods = module.TopLevelDecls.Where(d => d is LiteralModuleDecl).Select(d => d as LiteralModuleDecl).ToList();
    submods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (submods.Count() > 0) {
      summaries.Append(Heading3("Submodules")).Append(eol);
      foreach (var submod in submods) {
        var subinfo = ModuleInfo(submod, null);
        summaries.Append(subinfo.HtmlSummary);
        summaries.Append(br).Append(eol);
        info.Contents.Add(subinfo);
      }
    }
  }

  public bool IsType(TopLevelDecl t) {
    return (t is RevealableTypeDecl || t is SubsetTypeDecl);
  }

  /** Append the summary and detail information about type declarations to the string builders */
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
    var info = new Info();
    info.Contents = null;
    info.Kind = "const";
    info.Name = c.Name;
    info.FullName = c.FullDafnyName;
    info.Link = LinkTarget(c.FullDafnyName);

    info.RawLongDoc = Docstring(c);
    info.RawShortDoc = Shorten(info.RawLongDoc);

    var docstring = Docstring(c);
    var modifiers = c.ModifiersAsString();
    var linkedName = Code(Link(c.FullDafnyName, Bold(c.Name)));
    var linkedType = TypeLink(c.Type);
    var rhsstring = c.Rhs == null ? "" : (" := " + c.Rhs.ToString());

    info.HtmlSummary = linkedName + " : " + linkedType + DashShortDocstring(c);

    var details = new StringBuilder();
    var decl = modifiers + "const " + c.Name + ": " + linkedType + rhsstring;
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    var attributes = c.Attributes?.ToString();
    if (!String.IsNullOrEmpty(attributes)) {
      details.Append("Attributes: ").Append(Code(attributes)).Append(br).Append(eol);
    }
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    script.Append(ScriptEntry(info.FullName));
    return info;
  }

  public Info VarInfo(Field f, TopLevelDeclWithMembers owner) {
    var info = new Info();
    info.Contents = null;
    info.Kind = "var";
    info.Name = f.Name;
    info.FullName = f.FullDafnyName;
    info.Link = LinkTarget(f.FullDafnyName);

    info.RawLongDoc = Docstring(f);
    info.RawShortDoc = Shorten(info.RawLongDoc);

    var docstring = Docstring(f);
    var linkedName = Code(Link(f.FullDafnyName, Bold(f.Name)));
    var modifiers = f.ModifiersAsString();
    var linkedType = TypeLink(f.Type);

    info.HtmlSummary = linkedName + " : " + linkedType + DashShortDocstring(f); ;

    var details = new StringBuilder();
    var decl = modifiers + "var " + f.Name + ": " + linkedType;
    details.Append(Code(decl));
    details.Append(br).Append(eol);
    var attributes = f.Attributes?.ToString();
    if (!String.IsNullOrEmpty(attributes)) {
      details.Append("Attributes: ").Append(Code(attributes)).Append(br).Append(eol);
    }
    details.Append(IndentedHtml(docstring));
    info.HtmlDetail = details.ToString();
    script.Append(ScriptEntry(info.FullName));
    return info;
  }

  public Info ExecutableInfo(MemberDecl m, TopLevelDeclWithMembers owner) {
    var name = m.Name;
    if (m is Constructor) {
      if (name == "_ctor") {
        name = owner.Name;
        AddToIndexC(name, "_", owner.FullDafnyName, m.WhatKind);
      } else {
        name = owner.Name + "." + m.Name;
        AddToIndexC(name, m.Name, owner.FullDafnyName, m.WhatKind);
      }
      AddToIndex(name, owner.FullDafnyName, m.WhatKind);
    }

    var info = new Info();
    info.Contents = null;
    info.Kind = m.WhatKind;
    info.Name = name;
    info.FullName = m.FullDafnyName;
    info.Link = LinkTarget(m.FullDafnyName);

    var md = m as IHasDocstring;
    var docstring = Docstring(md);
    info.RawLongDoc = docstring;
    info.RawShortDoc = Shorten(docstring);

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

    var decl = modifiers + m.WhatKind + " " + ms;
    details.Append(Code(decl)).Append(br).Append(eol);

    var attributes = m.Attributes?.ToString();
    if (!String.IsNullOrEmpty(attributes)) {
      details.Append("Attributes: ").Append(Code(attributes)).Append(br).Append(eol);
    }
    details.Append(IndentedHtml(docstring));
    AppendSpecs(details, m);

    info.HtmlSummary = summaries.ToString();
    info.HtmlDetail = details.ToString();
    this.AllInfo.Add(info.FullName, info);
    script.Append(ScriptEntry(info.FullName));
    return info;
  }

  public Info TypeInfo(TopLevelDecl t, ModuleDefinition module, Info owner) {
    var link = Link(t.FullDafnyName, Code(Bold(t.Name)));

    AddToIndex(t.Name, module.FullDafnyName, t.WhatKind);
    var docstring = t is IHasDocstring ? Docstring(t as IHasDocstring) : "";
    // Note: Types do not have modifiers (at least at present)
    var modifiers = "";
    var typeparams = TypeFormals(t.TypeArgs);
    string kind = t.WhatKind.Replace("abstract", "").Replace("opaque", "");

    var info = new Info();
    info.Kind = t.WhatKind;
    info.Name = t.Name;
    info.FullName = t.FullDafnyName;
    info.Link = LinkTarget(info.FullName);
    info.RawLongDoc = docstring;
    info.RawShortDoc = Shorten(docstring);

    var details = new StringBuilder();

    info.HtmlSummary = ($"{Code(kind)} {Code(link + typeparams)} {DashShortDocstring(t as IHasDocstring)}");

    var decl = new StringBuilder();
    decl.Append(modifiers + kind + " " + t.Name);
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
    details.Append(Code(decl.ToString()));

    if (t is DatatypeDecl dt) {
      details.Append(TableStart());
      foreach (var ctor in dt.Ctors) {
        string sig = ctor.Name;
        if (ctor.Formals.Count > 0) {
          sig += "(" + String.Join(", ", ctor.Formals.Select(ff => FormalAsString(ff, false))) + ")";
        }
        string sinfo = mdash + ToHtml(Docstring(ctor)); // TODO - does this wrap OK in a table
        details.Append(Row(Code(Spaces(2) + "|" + Spaces(1)), ctor.IsGhost ? Code("ghost") : "", Code(sig), sinfo));
      }
      details.Append(TableEnd());
    }

    var attributes = t.Attributes?.ToString();
    if (!String.IsNullOrEmpty(attributes)) {
      details.Append(br).Append(eol);
      details.Append(space4).Append(Code(attributes)); // TODO - make like others
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

    //if (!AllInfo.ContainsKey(info.FullName)) {
    owner.Contents.Add(info);
    AllInfo.Add(info.FullName, info);
    //}
    info.HtmlDetail = details.ToString();
    script.Append(ScriptEntry(info.FullName));
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
        this.AllInfo.Add(info.FullName, info);
        AddToIndex(c.Name, decl.FullDafnyName, "const");

        var styledName = Code(Bold(c.Name));
        var linkedType = TypeLink(c.Type);

        summaries.Append(Row(Link(info.FullName, styledName), " : ", linkedType, DashShortDocstring(c))).Append(eol);

      }
      summaries.Append(TableEnd()).Append(eol);
    }
  }

  /** Append the summary and detail information about field declarations to the string builders */
  public void AddFieldSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var fields = decl.Members.Where(c => c is Field && c is not ConstantField && !IsGeneratedName(c.Name)).Select(c => c as Field).ToList();
    fields.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    if (fields.Count() > 0) {
      summaries.Append(Heading3("Mutable Fields\n"));
      summaries.Append(TableStart()).Append(eol);
      foreach (var c in fields) {
        var info = VarInfo(c, decl);
        ownerInfoList.Add(info);
        this.AllInfo.Add(info.FullName, info);
        AddToIndex(c.Name, decl.FullDafnyName, "var");

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

  public static bool IsGeneratedName(string name) {
    return (name.Length > 1 && name[0] == '_') || name.StartsWith("reveal_");
  }

  public void AddLemmaSummaries(TopLevelDeclWithMembers decl, StringBuilder summaries, List<Info> ownerInfoList) {
    var methods = decl.Members.Where(m => m is Method && (m as Method).IsLemmaLike && !IsGeneratedName(m.Name)).Select(m => m as MemberDecl).ToList();
    methods.Sort((f, ff) => f.Name.CompareTo(ff.Name));
    AddExecutableSummaries("Lemmas", methods, decl, summaries, ownerInfoList);
  }

  public string IndentedHtml(string docstring) {
    return IndentedHtml(docstring, false);
  }

  public string IndentedHtml(string docstring, bool nothingIfNull) {
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

  public void WriteTOC(List<LiteralModuleDecl> modules) {
    modules.Sort((k, m) => k.FullDafnyName.CompareTo(m.FullDafnyName));
    string filename = Outputdir + "/index.html";
    using StreamWriter file = new(filename);
    file.Write(HtmlStart($"Dafny Documentation{ProgramHeader()}", script.Append(ScriptEnd()).ToString()));

    file.Write(Heading1($"Dafny Documentation{ProgramHeader()}{space4}"));
    file.Write(BodyStart());
    file.Write(MainStart());
    file.WriteLine(ListStart());
    int currentIndent = 0;
    foreach (var module in modules) {
      var fullname = module.FullDafnyName;
      int level = Regex.Matches(fullname, "\\.").Count;
      while (level > currentIndent) {
        file.WriteLine(ListStart());
        currentIndent++;
      }
      while (level < currentIndent) {
        file.WriteLine(ListEnd());
        currentIndent--;
      }
      var ds = DashShortDocstring(module);
      if (module.ModuleDef.IsDefaultModule) {
        file.WriteLine(ListItem("Module " + Link(RootName, Code(RootName)) + ds));
      } else {
        file.WriteLine(ListItem("Module " + Link(fullname, Code(fullname)) + ds));
      }
    }
    file.WriteLine(ListEnd());
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
    //System.Console.WriteLine("ARROWP " + t + " " + t.GetType());

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
          //System.Console.WriteLine("DT " + udt + " " + udt.Name + " " + tt.GetType() + " " + udt.GetType());
          s = "(" + TypeActualParameters(t.TypeArgs, false) + ")";
        } else {
          s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
        }
      } else if (tt is TypeParameter) {
        s = tt.Name;
      } else if (tt is OpaqueTypeDecl) {
        s = Link(tt.FullDafnyName, tt.Name) + TypeActualParameters(t.TypeArgs);
      } else {
        System.Console.WriteLine("TUP " + udt + " " + udt.Name + " " + tt.GetType() + " " + udt.GetType());
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

  /** True for declarations that have their own page */
  public bool HasOwnPage(Declaration t) {
    if (t is LiteralModuleDecl) {
      return true;
    }
    return t is TopLevelDeclWithMembers && (t is ClassDecl || t is TraitDecl || (t as TopLevelDeclWithMembers).Members.Count() > 0);
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

  /** If there is a docstring, returns a dash + the abbreviated docstring + the more... link */
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

  // Used for declarations that merit their own page (modules, classes, traits, types with members, ...)
  // public String ShortAndMoreForDecl(TopLevelDecl d) {
  //   var docstring = Docstring(d as IHasDocstring);
  //   var shortstring = Shorten(docstring);
  //   String result = "";
  //   if (!String.IsNullOrEmpty(docstring)) {
  //     result = ToHtml(shortstring);
  //     if (shortstring != docstring) {
  //       result += " " + LinkToAnchor("decl-detail", "(more...)");
  //     }
  //   }
  //   return result;
  // }

  // public String ShortAndMore(IHasDocstring d, String target) {
  //   var docstring = Docstring(d);
  //   var shortstring = Shorten(docstring);
  //   String result = "";
  //   if (!String.IsNullOrEmpty(docstring)) {
  //     result = ToHtml(shortstring);
  //     if (shortstring != docstring) {
  //       result += $" <a href=\"#{target}\">(more...)</a>";
  //     }
  //   }
  //   return result;
  // }

  public String ReplaceFirst(string text, string old, string replacement) {
    var k = text.IndexOf(old);
    if (k == -1) {
      return text;
    }
    return text.Substring(0, k) + replacement + text.Substring(k + old.Length);
  }

  public static string QualifiedNameWithLinks(string fullName, bool alsoLast = true) {
    int hash = fullName.IndexOf('#');
    string tail = null;
    if (hash > 0) {
      fullName = fullName.Substring(0, hash);
      tail = fullName.Substring(hash + 1);
    }
    return QualifiedNameWithLinks(fullName, tail, alsoLast);
  }

  public static string QualifiedNameWithLinks(string fullName, string text, bool alsoLast = true) {
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

  /** Adds (a request for) an index entry, with a link to a file */
  public void AddToIndexF(string name, string target, string kind) {
    nameIndex.Add(name + " " + nameIndex.Count + " " + target, kind + " " + QualifiedNameWithLinks(target, name));
  }

  /** Adds (a request for) an index entry, with a link to a location in a file */
  public void AddToIndex(string inpageID, string owner, string kind) {
    nameIndex.Add(inpageID + " " + nameIndex.Count + " " + owner, kind + " " + QualifiedNameWithLinks(owner, inpageID));
  }

  public void AddToIndexC(string inpageID, string text, string owner, string kind) {
    nameIndex.Add(inpageID + " " + nameIndex.Count + " " + owner, kind + " " + QualifiedNameWithLinks(owner, text));
  }

  public void WriteIndex() {
    var keys = nameIndex.Keys.ToList();
    keys.Sort();

    string filename = Outputdir + "/nameindex.html";
    using StreamWriter file = new(filename);
    file.Write(HtmlStart($"Index for program {DafnyProgram.Name}"));
    file.Write(Heading1($"Index{ProgramHeader()}{space4}{Smaller(contentslink)}"));
    file.Write(BodyStart());
    file.Write(MainStart("full"));
    foreach (var key in keys) {
      var k = key.IndexOf(' ');
      var value = nameIndex[key]; // Already rewritten as a bunch of links
      var keyn = key.Substring(0, k);
      k = key.LastIndexOf(' ');
      var owner = key.Substring(k + 1);
      var hash = value.IndexOf('#');
      if (hash == -1) {
        file.Write($"<a href=\"{owner}.html\">{keyn}</a>");
      } else if (value.StartsWith("export")) {
        file.Write($"<a href=\"{owner}.html#{ExportSetAnchor(keyn)}\">{keyn}</a>");
      } else {
        var link = value.Substring(0, hash);
        file.Write($"<a href=\"{owner}.html#{keyn}\">{keyn}</a>");
      }
      file.WriteLine(mdash + value + br);
    }
    file.Write(MainEnd());
    file.Write(BodyAndHtmlEnd());
    AnnounceFile(filename);
  }

  public static string DefaultOutputDir = "./docs";
  public static readonly string RootName = "_"; // Name of file for root module
  static string contentslink = Link("index", "[table of contents]");
  static string indexlink = Link("nameindex", "[index]");
}