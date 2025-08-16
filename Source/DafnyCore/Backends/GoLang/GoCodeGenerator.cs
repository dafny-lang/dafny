//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Text.RegularExpressions;
using DafnyCore;
using DafnyCore.Options;
using JetBrains.Annotations;
using Tomlyn.Model;
using static Microsoft.Dafny.ConcreteSyntaxTreeUtils;

namespace Microsoft.Dafny.Compilers {
  class GoCodeGenerator : SinglePassCodeGenerator {
    protected override void EmitStaticExternMethodQualifier(string qual, ConcreteSyntaxTree wr) {
      if (qual != null) {
        qual = ImportPrefix + qual;
      }
      base.EmitStaticExternMethodQualifier(qual, wr);
    }

    protected override bool RequiresAllVariablesToBeUsed => true;
    private string DafnyRuntimeGoModule = "github.com/dafny-lang/DafnyRuntimeGo/v4/";

    private bool GoModuleMode;
    private string GoModuleName;
    public GoCodeGenerator(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
      var goModuleName = Options.Get(GoBackend.GoModuleNameCliOption);
      GoModuleMode = goModuleName != null;
      if (GoModuleMode) {
        GoModuleName = goModuleName.ToString();
      }
      if (Options?.CoverageLegendFile != null) {
        //TODO: What's the module name for this?
        ImportsNotFromDafnyModules.Add(new Import { Name = "DafnyProfiling", Path = "DafnyProfiling" });
      }
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.MethodSynthesis,
      Feature.ExternalConstructors,
      Feature.SubsetTypeTests,
      Feature.AllUnderscoreExternalModuleNames,
      Feature.RuntimeCoverageReport,
      Feature.StandardLibrariesActionsExterns
    };

    public override string ModuleSeparator => "_";
    protected override string IsMethodName => "Is_";

    string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter || tp is AbstractTypeDecl);
      return $"_default_{tp.GetCompileName(Options)}";
    }

    private readonly Dictionary<ModuleDefinition, Import> ModuleImports = new();
    private readonly List<Import> ImportsNotFromDafnyModules = [.. StandardImports];
    private string ModuleName;
    private ModuleDefinition CurrentModule;
    private ConcreteSyntaxTree RootImportWriter;
    private ConcreteSyntaxTree RootImportDummyWriter;

    private string MainModuleName;
    private static List<Import> StandardImports = [
      new Import { Name = "os", Path = "os" }
    ];
    private static string DummyTypeName = "Dummy__";

    private static string ImportPrefix = "m_";
    private struct Import {
      public string Name, Path;
      public ModuleDefinition ExternModule;
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("// Dafny program {0} compiled into Go", program.Name);

      CurrentModule = null;
      ModuleName = MainModuleName = program.MainMethod != null ? "main" : TransformToClassName(Path.GetFileNameWithoutExtension(program.Name));

      wr.WriteLine("package {0}", ModuleName);
      wr.WriteLine();

      string path;
      if (Options.IncludeRuntime) {
        EmitRuntimeSource("DafnyRuntimeGo", wr);
        path = GoModuleMode ? GoModuleName + "/" : "";
      } else {
        path = GoModuleMode ? DafnyRuntimeGoModule : "";
      }
      ImportsNotFromDafnyModules.Add(new Import { Name = "_dafny", Path = $"{path}dafny" });

      if (Options.Get(CommonOptionBag.UseStandardLibraries) && Options.Get(CommonOptionBag.TranslateStandardLibrary)) {
        EmitRuntimeSource("DafnyStandardLibraries_go", wr);
      }

      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter, out RootImportDummyWriter);
    }

    private string DafnyTypeDescriptor => $"{HelperModulePrefix}TypeDescriptor";

    // The implementation of seq<T> is now in DafnyRuntimeDafny/src/dafnyRuntime.dfy.
    // We have to special-case compiling this code a little bit in places to work around
    // features Dafny doesn't support, such as customizing the definition of equality.
    private bool IsDafnySequence(TopLevelDecl d) =>
      Options.Get(DeveloperOptionBag.Bootstrapping) && d.GetFullCompileName(Options) == "dafny.Sequence";

    private string DafnySequenceCompanion => $"{HelperModulePrefix}Companion_Sequence_";

    void EmitModuleHeader(ConcreteSyntaxTree wr) {
      wr.WriteLine("// Package {0}", ModuleName);
      wr.WriteLine("// Dafny module {0} compiled into Go", ModuleName);
      wr.WriteLine();
      wr.WriteLine("package {0}", ModuleName);
      wr.WriteLine();
      // This is a non-main module; it only imports things declared before it, so we don't need these writers
      EmitImports(wr, out _, out _);
      wr.WriteLine();
      wr.WriteLine("type {0} struct{{}}", DummyTypeName);
      wr.WriteLine();
    }

    void EmitImports(ConcreteSyntaxTree wr, out ConcreteSyntaxTree importWriter, out ConcreteSyntaxTree importDummyWriter) {
      wr.WriteLine("import (");
      importWriter = wr.Fork(1);
      wr.WriteLine(")");
      importDummyWriter = wr.Fork();
      if (ModuleName != "dafny") {
        foreach (var import in ImportsNotFromDafnyModules.Concat(ModuleImports.Values)) {
          EmitImport(import, importWriter, importDummyWriter);
        }
      }
    }

    public string TransformToClassName(string baseName) =>
      IdProtect(Regex.Replace(baseName, "[^_A-Za-z0-9$]", "_"));

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      CurrentModule = null;
      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), wr, mainMethod.Origin, mainMethod);

      var wBody = wr.NewNamedBlock("func main()");
      wBody.WriteLine("defer _dafny.CatchHalt()");

      var idName = IssueCreateStaticMain(mainMethod) ? "Main" : IdName(mainMethod);

      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{companion}.{idName}({GetHelperModuleName()}.{CharMethodQualifier}FromMainArguments(os.Args))");
      Coverage.EmitTearDown(wBody);
    }

    ConcreteSyntaxTree CreateDescribedSection(string desc, ConcreteSyntaxTree wr, params object[] args) {
      var body = wr.Fork();
      var str = string.Format(desc, args);
      body.WriteLine("// Definition of {0}", str);
      wr.WriteLine("// End of {0}", str);
      return body;
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var wr = ((GoCodeGenerator.ClassWriter)cw).ConcreteMethodWriter;
      return wr.NewNamedBlock("func (_this * {0}) Main({1} _dafny.Sequence)", FormatCompanionTypeName(((GoCodeGenerator.ClassWriter)cw).ClassName), argsParameterName);
    }

    private Import CreateImport(string moduleName, ModuleDefinition externModule,
      string /*?*/ libraryName) {
      string pkgName;
      if (libraryName != null) {
        pkgName = libraryName;
      } else {
        // Go ignores all filenames starting with underscores.  So we're forced
        // to rewrite "__default" to "default__".
        pkgName = moduleName;
        if (pkgName != "" && pkgName.All(c => c == '_')) {
          throw new UnsupportedFeatureException(Token.NoToken, Feature.AllUnderscoreExternalModuleNames,
            $"Cannot have a package name with only underscores: {pkgName}");
        }
        while (pkgName.StartsWith("_")) {
          pkgName = pkgName.Substring(1) + "_";
        }
      }


      return new Import { Name = ImportPrefix + moduleName, Path = pkgName, ExternModule = externModule };
    }

    protected override bool ShouldCompileModule(Program program, ModuleDefinition module) {
      if (!base.ShouldCompileModule(program, module)) {
        return false;
      }

      if (TranslationRecord.ModuleEmptyForCompilation(module)) {
        return false;
      }

      return true;
    }

    protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
      ModuleDefinition externModule,
      string libraryName /*?*/, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }

      var goModuleName = GoModuleMode ? GoModuleName + "/" : "";
      if (moduleName.Equals("_System")) {
        if (Options.IncludeRuntime) {
          goModuleName = GoModuleMode ? GoModuleName + "/" : "";
        } else {
          goModuleName = GoModuleMode ? DafnyRuntimeGoModule : "";
        }
      }
      ModuleName = PublicModuleIdProtect(moduleName);
      CurrentModule = module;
      var import = CreateImport(ModuleName, externModule, libraryName);
      var filename = string.Format("{0}/{0}.go", import.Path);
      var w = wr.NewFile(filename);
      EmitModuleHeader(w);

      import.Path = goModuleName + import.Path;
      AddImport(module, import);

      return w;
    }

    protected override void DependOnModule(Program program, ModuleDefinition module, ModuleDefinition externModule,
      string libraryName) {

      if (externModule == null && TranslationRecord.ModuleEmptyForCompilation(module)) {
        return;
      }

      var goModuleName = "";
      if (GoModuleMode) {
        // "_System" module has a special handling because although it gets translated from a Dafny module,
        // it is still part of the Dafny Runtime lib so has no associated go module name. It either uses the
        // project module name if embedded or falls back to the Runtime module name.
        if (module.GetCompileName(Options).Equals("_System")) {
          if (Options.IncludeRuntime) {
            goModuleName = GoModuleName + "/";
          } else {
            goModuleName = DafnyRuntimeGoModule;
          }
        } else {
          // For every other Dafny Module, fetch the associated go module name from the dtr structure.
          var translatedRecord = program.Compilation.AlreadyTranslatedRecord;
          translatedRecord.OptionsByModule.TryGetValue(module.FullDafnyName, out var moduleOptions);
          object moduleName = null;
          moduleOptions?.TryGetValue(GoBackend.GoModuleNameCliOption.Name, out moduleName);

          goModuleName = moduleName is string name ? moduleName + "/" : "";
          if (String.IsNullOrEmpty(goModuleName)) {
            Reporter.Warning(MessageSource.Compiler, ResolutionErrors.ErrorId.none, Token.Cli,
              $"Go Module Name not found for the module {module.GetCompileName(Options)}");
          }
        }
      }

      var publicModuleName = PublicModuleIdProtect(module.GetCompileName(Options));
      var import = CreateImport(publicModuleName, externModule, libraryName);
      import.Path = goModuleName + import.Path;
      AddImport(module, import);
    }

    protected override void FinishModule() {
      CurrentModule = null;
      ModuleName = MainModuleName;
    }

    private void AddImport(ModuleDefinition module, Import import) {
      // Import in root module
      EmitImport(import, RootImportWriter, RootImportDummyWriter);
      // Import in all subsequent modules
      ModuleImports[module] = import;
      var implemented = module.GetImplementedModule();
      while (implemented != null) {
        ModuleImports[implemented] = import;
        implemented = implemented.GetImplementedModule();
      }
    }

    private void EmitImport(Import import, ConcreteSyntaxTree importWriter, ConcreteSyntaxTree importDummyWriter) {
      var id = IdProtect(import.Name);
      var path = import.Path;

      importWriter.WriteLine("{0} \"{1}\"", id, path);

      bool isType;
      string memberName = null;
      if (id == "os") {
        memberName = "Args";
        isType = false;
      } else {
        isType = true;
        if (import.ExternModule != null) {
          var attributes = Attributes.Find(import.ExternModule.Attributes, "dummyImportMember");
          if (attributes != null && attributes.Args.Count == 2) {
            if (attributes.Args[0] is LiteralExpr expr1 && expr1.Value is string isNameValue &&
              attributes.Args[1] is LiteralExpr expr2 && expr2.Value is bool isTypeValue) {
              memberName = isNameValue;
              isType = isTypeValue;
            }
          }
        } else {
          memberName = DummyTypeName;
        }
      }

      if (memberName != null) {
        if (isType) {
          importDummyWriter.WriteLine("var _ {0}.{1}", id, memberName);
        } else {
          importDummyWriter.WriteLine("var _ = {0}.{1}", id, memberName);
        }
      }
    }

    protected override string GetHelperModuleName() => "_dafny";

    private string HelperModulePrefix => ModuleName == "dafny" ? "" : $"{GetHelperModuleName()}.";

    protected override IClassWriter CreateClass(string moduleName, bool isExtern, string/*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      var isDefaultClass = cls is DefaultClassDecl;

      bool isSequence = superClasses.Any(superClass => superClass is UserDefinedType udt && IsDafnySequence(udt.ResolvedClass));
      return CreateClass(cls, isExtern, fullPrintName, typeParameters, superClasses, tok, wr, includeRtd: !isDefaultClass, includeEquals: !isSequence, includeString: !isSequence);
    }

    // TODO Consider splitting this into two functions; most things seem to be passing includeRtd: false, includeEquals: false and includeString: true.
    private GoCodeGenerator.ClassWriter CreateClass(TopLevelDecl classContext, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, IOrigin tok, ConcreteSyntaxTree wr, bool includeRtd, bool includeEquals, bool includeString) {
      // See docs/Compilation/ReferenceTypes.md for a description of how instance members of classes and traits are compiled into Go.
      //
      // func New_Class_(Type0 _dafny.TypeDescriptor, Type1 _dafny.TypeDescriptor) *Class {
      //   _this := Class{}
      //
      //   // Have to do it this way because some default values (namely type
      //   // parameters) assume that _this points to the current value
      //   _this.Type0 = Type0
      //   _this.Type1 = Type1
      //   _this.Field0 = ...
      //   _this.Field1 = ...
      //   return &_this
      // }
      //
      // func (_this *Class) InstanceMethod(param0 type0, ...) returnType {
      //   ...
      // }
      //
      // func (_this *CompanionStruct_Class) StaticMethod(param0 type0, ...) returnType {
      //   ...
      // }
      //
      // func (*Class) String() string {
      //   return "module.Class"
      // }
      //
      // func Type_Class_(Type0 _dafny.TypeDescriptor, Type1 _dafny.TypeDescriptor) _dafny.TypeDescriptor {
      //   return type_Class_{Type0, Type1}
      // }
      //
      // type type_Class_ struct{
      //   Type0 _dafny.TypeDescriptor
      //   Type1 _dafny.TypeDescriptor
      // }
      //
      // func (_this type_Class_) Default() any {
      //   return (*Class)(nil)
      // }
      //
      // func (_this type_Class_) String() string {
      //   return "module.Class"
      // }
      //
      var name = Capitalize(IdName(classContext));

      var w = CreateDescribedSection("class {0}", wr, name);

      var instanceFieldWriter = w.NewBlock(string.Format("type {0} struct", name));

      w.WriteLine();
      CreateInitializer(classContext, name, w, out var instanceFieldInitWriter, out var traitInitWriter, out var rtdParamWriter);

      var isNewtypeWithTraits = classContext is NewtypeDecl { Traits: { Count: > 0 } };

      var rtdCount = 0;
      if (typeParameters != null) {
        rtdCount = WriteRuntimeTypeDescriptorsFields(typeParameters, false, instanceFieldWriter, instanceFieldInitWriter, rtdParamWriter);
      }
      if (isNewtypeWithTraits) {
        var udt = UserDefinedType.FromTopLevelDecl(classContext.Origin, classContext);
        rtdParamWriter.Write($"value {TypeName(udt, rtdParamWriter, classContext.Origin)}");
      }

      w.WriteLine();
      var staticFieldWriter = w.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      var staticFieldInitWriter = w.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));

      if (includeEquals) {
        // This Equals() is so simple that we could just use == instead, but uniformity is good and it'll get inlined anyway.

        w.WriteLine();
        var wEquals = w.NewNamedBlock("func (_this *{0}) Equals(other *{0}) bool", name);
        wEquals.WriteLine("return _this == other");

        w.WriteLine();
        var wEqualsGeneric = w.NewNamedBlock("func (_this *{0}) EqualsGeneric(x interface{{}}) bool", name);
        wEqualsGeneric.WriteLine("other, ok := x.(*{0})", name);
        wEqualsGeneric.WriteLine("return ok && _this.Equals(other)");
      }

      w.WriteLine();
      if (includeString) {
        if (isNewtypeWithTraits) {
          var wString = w.NewNamedBlock("func (_this *{0}) String() string", name);
          wString.WriteLine("return _dafny.String(_this._value)");
        } else {
          var wString = w.NewNamedBlock("func (*{0}) String() string", name);
          // Be consistent with other back ends, which don't fold _module into the main module
          var module = ModuleName == MainModuleName ? "_module" : ModuleName;
          wString.WriteLine("return \"{0}.{1}\"", module, name);
        }
      }

      if (includeRtd) {
        CreateRTD(name, typeParameters, out var wDefault, w);

        wDefault.WriteLine("return (*{0})(nil)", name);
      }

      var cw = new ClassWriter(this, classContext, tok != null, name, isExtern, null, w, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);

      if (superClasses != null) {
        superClasses = superClasses.Where(trait => !trait.IsObject).ToList();
        EmitParentTraits(tok, name, true, superClasses, w);
      }
      return cw;
    }

    private void EmitParentTraits(IOrigin tok, string childName, bool childIsUsedAsPointer, List<Type> parentTraits, ConcreteSyntaxTree wr) {
      var star = childIsUsedAsPointer ? "*" : "";
      var addressOf = childIsUsedAsPointer ? "&" : "";
      // Emit a method that returns the ID of each parent trait
      var parentTraitsWriter = wr.NewBlock($"func (_this {star}{childName}) ParentTraits_() []*{HelperModulePrefix}TraitID");
      parentTraitsWriter.WriteLine("return [](*{0}TraitID){{{1}}};", HelperModulePrefix, Util.Comma(parentTraits, parent => {
        var trait = ((UserDefinedType)parent).ResolvedClass;
        return TypeName_Companion(trait, parentTraitsWriter, tok) + ".TraitID_";
      }));

      foreach (Type typ in parentTraits) {
        // Emit a compile-time sanity check that the class emitted does indeed have the methods required by the parent trait
        wr.WriteLine($"var _ {TypeName(typ, wr, tok)} = {addressOf}{childName}{{}}");
      }

      wr.WriteLine($"var _ {HelperModulePrefix}TraitOffspring = {addressOf}{childName}{{}}");

      wr.WriteLine();
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TraitDecl trait, List<Type> superClasses /*?*/, IOrigin tok, ConcreteSyntaxTree wr) {
      //
      // type Trait interface {
      //   String() string
      //   AbstractMethod0(param0 type0, ...) returnType0
      //   ...
      // }
      //
      // type companionStruct_Trait_ struct {
      //   StaticField0 type0
      //   StaticField1 type1
      //   ...
      // }
      //
      // var Companion_Trait_ = companionStruct_Trait{
      //   StaticField0: ...,
      //   StaticField1: ...,
      // }
      //
      // func (_static *companionStruct_Trait) CastTo_(x any) Trait {
      //   var t Trait
      //   t, _ = x.(Trait)
      //   return t
      // }
      //
      // func (_static *companionStruct_Trait) ConcreteInstanceMethod(_this Trait, ...) ... {
      //   ...
      // }
      //
      // func (_static *companionStruct_Trait) StaticMethod(...) ... {
      //   ...
      // }
      wr = CreateDescribedSection("trait {0}", wr, name);
      var abstractMethodWriter = wr.NewNamedBlock("type {0} interface", name);
      var concreteMethodWriter = wr.Fork();
      abstractMethodWriter.WriteLine("String() string");
      if (IsDafnySequence(trait)) {
        abstractMethodWriter.WriteLine("Equals(other Sequence) bool");
        abstractMethodWriter.WriteLine("EqualsGeneric(x interface{}) bool");
        abstractMethodWriter.WriteLine("VerbatimString(isLiteral bool) string");
      }

      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));
      var wCastTo = wr.NewNamedBlock("func ({0}) CastTo_(x interface{{}}) {1}", FormatCompanionTypeName(name), name);
      wCastTo.WriteLine("var t {0}", name);
      wCastTo.WriteLine("t, _ = x.({0})", name);
      wCastTo.WriteLine("return t");


      var cw = new ClassWriter(this, trait, false, name, isExtern, abstractMethodWriter, concreteMethodWriter, null, null, null, staticFieldWriter, staticFieldInitWriter);
      staticFieldWriter.WriteLine($"TraitID_ *{HelperModulePrefix}TraitID");
      staticFieldInitWriter.WriteLine($"TraitID_: &{HelperModulePrefix}TraitID{{}},");
      return cw;
    }

    protected void CreateInitializer(TopLevelDecl classContext, string name, ConcreteSyntaxTree wr,
      out ConcreteSyntaxTree instanceFieldInitWriter, out ConcreteSyntaxTree traitInitWriter, out ConcreteSyntaxTree rtdParamWriter) {
      wr.Write("func {0}(", FormatInitializerName(name));
      rtdParamWriter = wr.Fork();
      var w = wr.NewNamedBlock(") *{0}", name);
      var parameters = classContext is NewtypeDecl { Traits: { Count: > 0 } } ? "value" : "";
      w.WriteLine($"_this := {name}{{{parameters}}}");

      w.WriteLine();
      instanceFieldInitWriter = w.Fork();
      traitInitWriter = w.Fork();
      w.WriteLine("return &_this");
    }

    protected override bool SupportsProperties => false;

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      // FIXME: There should be tests to make sure that the finalizer mechanism achieves what I hope it does, namely allowing the iterator's goroutine to be garbage-collected along with the iterator.
      //
      // type MyIteratorExample struct {
      //   cont chan<- struct{}
      //   yielded <-chan struct{}
      //
      //   // Fields
      // }
      //
      // func (_this * MyIteratorExample) Ctor__(/* params */) {
      //   _cont := make(chan struct{})
      //   _yielded := make(chan struct{})
      //   _this.cont = _cont
      //   _this.yielded = _yielded
      //   // assign params
      //
      //   go _this.run(_cont, _yielded)
      //
      //   _dafny.SetFinalizer(this_, func(_ MyIteratorExample) {
      //     close(_cont) // will cause the iterator to return and close _yielded
      //   })
      // }
      //
      // func (_this * MyIteratorExample) MoveNext() bool {
      //   _this.cont <- struct{}{}
      //   _, ok <- _this.yielded
      //
      //   return ok
      // }
      //
      // func (_this * MyIteratorExample) run(_cont <-chan struct{}, _yielded chan<- struct{}) {
      //   defer close(_yielded)
      //
      //   var _ok bool
      //   _, _ok = <- _cont
      //   if !_ok { return }
      //
      //   // Statements ... yield becomes:
      //   _yielded <- struct{}{}
      //   _, _ok = <- _cont
      //   if !_ok { return }
      //
      //   // break becomes:
      //   return
      // }()
      var cw = CreateClass(iter, false, null, iter.TypeArgs, null, null, wr, includeRtd: false, includeEquals: false, includeString: true);

      cw.InstanceFieldWriter.WriteLine("cont chan<- struct{}");
      cw.InstanceFieldWriter.WriteLine("yielded <-chan struct{}");

      Constructor ct = null;
      foreach (var member in iter.Members) {
        if (member is Field f && !f.IsGhost) {
          cw.DeclareField(IdName(f), iter, false, false, f.Type, f.Origin, PlaceboValue(f.Type, wr, f.Origin, true), f);
        } else if (member is Constructor c) {
          Contract.Assert(ct == null);
          ct = c;
        }
      }
      Contract.Assert(ct != null);

      cw.ConcreteMethodWriter.Write("func (_this * {0}) {1}(", IdName(iter), IdName(ct));
      string sep = "";
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          // here we rely on the parameters and the corresponding fields having the same names
          cw.ConcreteMethodWriter.Write("{0}{1} {2}", sep, IdName(p), TypeName(p.Type, wr, p.Origin));
          sep = ", ";
        }
      }
      var wCtor = cw.ConcreteMethodWriter.NewBlock(")");
      wCtor.WriteLine("_cont := make(chan struct{})");
      wCtor.WriteLine("_yielded := make(chan struct{})");
      wCtor.WriteLine("_this.cont = _cont");
      wCtor.WriteLine("_this.yielded = _yielded");
      wCtor.WriteLine();
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          wCtor.WriteLine("_this.{0} = {1}", Capitalize(IdName(p)), IdName(p));
        }
      }
      wCtor.WriteLine();
      wCtor.WriteLine("go _this.run(_cont, _yielded)");
      wCtor.WriteLine();
      wCtor.WriteLine("_dafny.SetFinalizer(_this, func(_ * {0}) {{ close(_cont) }})", IdName(iter));

      var wMoveNext = cw.ConcreteMethodWriter.NewNamedBlock("func (_this * {0}) MoveNext() bool", IdName(iter));
      wMoveNext.WriteLine("_this.cont <- struct{}{}");
      wMoveNext.WriteLine("_, ok := <- _this.yielded");
      wMoveNext.WriteLine();
      wMoveNext.WriteLine("return ok");

      var wRun = cw.ConcreteMethodWriter.NewNamedBlock("func (_this * {0}) run(_cont <-chan struct{{}}, _yielded chan<- struct{{}})", IdName(iter));
      wRun.WriteLine("defer close(_yielded)");
      wRun.WriteLine();
      wRun.WriteLine("_, _ok := <- _cont");
      wRun.WriteLine("if !_ok { return }");
      wRun.WriteLine();

      return wRun;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      // ===== For inductive datatypes:
      //
      // type Dt struct {
      //   Data_Dt_
      // }
      //
      // type Data_Dt_ interface {
      //   isDt()
      // }
      //
      // // For uniformity with co-datatypes
      // func (_this Dt) Get_() Data_Dt_ {
      //   return _this.Data_Dt_
      // }
      //
      // type CompanionStruct_Dt_ struct {}
      //
      // var Companion_Dt_ = CompanionStruct_Dt_ {}
      //
      // ...
      //
      // type Dt_Ctor0 struct {
      //   Field0 type0
      //   Field1 type1
      //   ...
      // }
      //
      // func (Dt_Ctor0) isDt() {}
      //
      // func (_ CompanionStruct_Dt_) CreateCtor0(field0 type0, field1 type1) Dt {
      //   return Dt{Dt_Ctor0{type0, type1}}
      // }
      //
      // func (_this Dt) IsCtor0() bool {
      //   _, ok := _this.Data_Dt_.(Dt_Ctor0)
      //   return ok
      // }
      //
      // type Dt_Ctor1 struct {
      //   ...
      // }
      //
      // ...
      //
      // func (_this Dt) DtorDtor0() (dtor0Type, bool) {
      //   return _this.Data_Dt_.(Dt_Ctor0).Field0
      // }
      //
      // func (_this Dt) DtorDtor1() (dtor1Type, bool) {
      //   switch data := _this.Data_Dt_.(type) {
      //   case Dt_Ctor0:
      //     return data.Field1
      //   default:
      //     return data.(Dt_Ctor1).Field0
      //   }
      // }
      //
      // func (_this Dt) String() { ... }
      //
      // func (_this Dt) EqualsGeneric(other any) bool { ... }
      //
      // func (CompanionStruct_Dt_) AllSingletonConstructors() _dafny.Iterator {
      //   i := -1
      //   return func() (any, bool) {
      //     i++
      //     switch i {
      //       case 0:
      //         return Companion_Dt_.Create_Ctor0(), true
      //       case 1:
      //         return Companion_Dt_.Create_Ctor1(), true
      //       ...
      //       default:
      //         return Dt{}, false
      //     }
      //   }
      // }
      //
      // func Type_Dt_(tyArg0 Type, tyArg1 Type, ...) _dafny.TypeDescriptor {
      //   return type_Dt_{tyArg0, tyArg1, ...}
      // }
      //
      // type type_Dt_ struct {
      //   tyArg0 Type
      //   tyArg1 Type
      // }
      //
      // func (ty type_Dt_) Default() any {
      //   tyArg0 := ty.tyArg0
      //   tyArg1 := ty.tyArg1
      //   return Companion_Dt_.Create_CtorK(...)
      // }
      //
      // func (ty type_Dt_) String() string {
      //   return "module.Dt"
      // }
      //
      // TODO Optimize record types
      //
      // ===== For co-inductive datatypes:
      //
      // type Dt struct {
      //   Iface_Dt_
      // }
      //
      // type Iface_Dt_ interface {
      //   Get_() Data_Dt_
      // }
      //
      // type lazyDt struct {
      //   value Iface_Dt_
      //   init func() Dt
      // }
      //
      // func (_this * lazyDt) Get_() *Iface_Dt {
      //   if _this.value == nil {
      //      _this.value = _this.init().Get_()
      //      _this.init = nil // allow GC of values in closure
      //   }
      //   return _this.value
      // }
      //
      // ...
      //
      // func (_ CompanionStruct_Dt_) LazyDt(f func() Dt) Dt {
      //   return Dt{*lazyDt{nil, f}}
      // }
      //
      // func (_ CompanionStruct_Dt_) CreateCtor0(field0 type0, field1 type1) Dt {
      //   return Dt{*Dt_Ctor0{type0, type1}}
      // }
      //
      // func (_this * Dt_Ctor0) Get_() Dt {
      //   return _this
      // }
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.go
        return null;
      }

      string name = Capitalize(dt.GetCompileName(Options));
      string companionTypeName = FormatCompanionTypeName(name);
      string dataName = FormatDatatypeInterfaceName(name);
      string ifaceName = FormatLazyInterfaceName(name);
      var simplifiedType = DatatypeWrapperEraser.SimplifyType(Options, UserDefinedType.FromTopLevelDecl(dt.Origin, dt));
      var simplifiedTypeName = TypeName(simplifiedType, wr, dt.Origin);

      string StructOfCtor(DatatypeCtor ctor) {
        return string.Format("{0}{1}_{2}", dt is CoDatatypeDecl ? "*" : "", name, ctor.GetCompileName(Options));
      }

      // from here on, write everything into the new block created here:
      wr = CreateDescribedSection("{0} {1}", wr, dt.WhatKind, name);

      if (dt is IndDatatypeDecl) {
        var wStruct = wr.NewNamedBlock("type {0} struct", name);
        WriteRuntimeTypeDescriptorsFields(dt.TypeArgs, false, wStruct, null, null);
        wStruct.WriteLine(dataName);

        wr.WriteLine();
        var wGet = wr.NewNamedBlock("func (_this {0}) Get_() {1}", name, dataName);
        wGet.WriteLine("return _this.{0}", dataName);
      } else {
        var wDt = wr.NewNamedBlock("type {0} struct", name);
        WriteRuntimeTypeDescriptorsFields(dt.TypeArgs, false, wDt, null, null);
        wDt.WriteLine(ifaceName);

        wr.WriteLine();
        var wIface = wr.NewNamedBlock("type {0} interface", ifaceName);
        wIface.WriteLine("Get_() {0}", dataName);

        wr.WriteLine();
        var wLazy = wr.NewNamedBlock("type lazy_{0}_ struct", name);
        wLazy.WriteLine("value {0}", dataName);
        wLazy.WriteLine("init func() {0}", name);

        wr.WriteLine();
        var wLazyGet = wr.NewNamedBlock("func (_this *lazy_{0}_) Get_() {1}", name, dataName);
        var wIf = wLazyGet.NewBlock("if _this.value == nil");
        wIf.WriteLine("_this.value = _this.init().Get_()");
        wIf.WriteLine("_this.init = nil"); // allow GC of values in closure

        wLazyGet.WriteLine("return _this.value");

        wr.WriteLine();
        var typeDescriptorCount = WriteRuntimeTypeDescriptorsFormals(dt.TypeArgs, false, out var wrFormals, out var wrActuals);
        var sep = typeDescriptorCount > 0 ? ", " : "";
        var wLazyCreate = wr.NewNamedBlock($"func ({companionTypeName}) {FormatLazyConstructorName(name)}({wrFormals}{sep}f func () {name}) {name}");
        wLazyCreate.WriteLine($"return {name}{{{wrActuals}{sep}&lazy_{name}_{{nil, f}}}}");
      }

      {
        wr.WriteLine();
        var wIface = wr.NewNamedBlock("type {0} interface", dataName);
        wIface.WriteLine("is{0}()", name);
      }

      wr.WriteLine();
      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", companionTypeName);
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), companionTypeName);

      string typeDescriptorDeclarations;
      string typeDescriptorUses;
      {
        WriteRuntimeTypeDescriptorsFormals(dt.TypeArgs, false, out var wTypeDescriptorDeclarations, out var wTypeDescriptorUses);
        typeDescriptorDeclarations = wTypeDescriptorDeclarations.ToString();
        typeDescriptorUses = wTypeDescriptorUses.ToString();
      }

      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        var ctorStructName = name + "_" + ctor.GetCompileName(Options);
        wr.WriteLine();
        var wStruct = wr.NewNamedBlock("type {0} struct", ctorStructName);
        var k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            wStruct.WriteLine("{0} {1}", DatatypeFieldName(formal, k), TypeName(formal.Type, wr, formal.Origin));
            k++;
          }
        }

        wr.WriteLine();
        wr.WriteLine("func ({0}{1}) is{2}() {{}}", dt is CoDatatypeDecl ? "*" : "", ctorStructName, name);
        wr.WriteLine();

        wr.Write($"func ({companionTypeName}) {FormatDatatypeConstructorName(ctor.GetCompileName(Options))}({typeDescriptorDeclarations}");
        var sep = typeDescriptorDeclarations.Length != 0 ? ", " : "";
        var argNames = new List<string>();
        k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            var formalName = DatatypeFieldName(formal, k);

            wr.Write($"{sep}{formalName} {TypeName(formal.Type, wr, formal.Origin)}");

            argNames.Add(formalName);
            sep = ", ";
            k++;
          }
        }
        var wCreateBody = wr.NewNamedBlock(") {0}", name);
        sep = typeDescriptorDeclarations.Length != 0 ? ", " : "";
        var co = dt is CoDatatypeDecl ? "&" : "";
        wCreateBody.WriteLine($"return {name}{{{typeDescriptorUses}{sep}{co}{ctorStructName}{{{Util.Comma(argNames)}}}}}");

        wr.WriteLine();
        var wCheck = wr.NewNamedBlock("func (_this {0}) {1}() bool", name, FormatDatatypeConstructorCheckName(ctor.GetCompileName(Options)));
        wCheck.WriteLine("_, ok := _this.Get_().({0})", StructOfCtor(ctor));
        wCheck.WriteLine("return ok");

        if (dt is CoDatatypeDecl) {
          wr.WriteLine();
          var wGet = wr.NewNamedBlock("func (_this *{0}) Get_() {1}", ctorStructName, dataName);
          wGet.WriteLine("return _this");
        }
      }

      /* func (_static CompanionStruct_Dt_) Default(_default_A any, _default_B any) Dt {
       *   return Dt{Dt_GroundingCtor{...}}
       * }
       */
      wr.WriteLine();
      wr.Write($"func ({companionTypeName}) Default({typeDescriptorDeclarations}");
      var usedParameters = UsedTypeParameters(dt);
      if (typeDescriptorDeclarations.Length != 0 && usedParameters.Count != 0) {
        wr.Write(", ");
      }
      wr.Write(usedParameters.Comma(tp => $"{FormatDefaultTypeParameterValue(tp)} interface{{}}"));
      {
        var wDefault = wr.NewBlock($") {simplifiedTypeName}");
        wDefault.Write("return ");
        var groundingCtor = dt.GetGroundingCtor();
        if (groundingCtor.IsGhost) {
          wDefault.Write(ForcePlaceboValue(simplifiedType, wDefault, dt.Origin));
        } else if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(Options, dt, out var innerType)) {
          wDefault.Write(DefaultValue(innerType, wDefault, dt.Origin));
        } else {
          var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
          var arguments = nonGhostFormals.Comma(f => DefaultValue(f.Type, wDefault, f.Origin));
          EmitDatatypeValue(dt, groundingCtor, dt is CoDatatypeDecl, typeDescriptorUses, arguments, wDefault);
        }
        wDefault.WriteLine();
      }

      if (dt.HasFinitePossibleValues) {
        wr.WriteLine();
        var wSingles = wr.NewNamedBlock("func (_ {0}) AllSingletonConstructors() _dafny.Iterator", companionTypeName);
        wSingles.WriteLine("i := -1");
        wSingles = wSingles.NewNamedBlock("return func() (interface{{}}, bool)");
        wSingles.WriteLine("i++");
        wSingles = wSingles.NewNamedBlock("switch i");
        var i = 0;
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          wSingles.WriteLine("case {0}: return {1}.{2}(), true", i, FormatCompanionName(name), FormatDatatypeConstructorName(ctor.GetCompileName(Options)));
          i++;
        }
        wSingles.WriteLine("default: return {0}{{}}, false", name);
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors.Where(dtor => dtor.EnclosingCtors[0] == ctor)) {
          var compiledConstructorCount = dtor.EnclosingCtors.Count(constructor => !constructor.IsGhost);
          if (compiledConstructorCount != 0) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              wr.WriteLine();
              var wDtor = wr.NewNamedBlock("func (_this {0}) {1}() {2}", name, FormatDatatypeDestructorName(arg.CompileName), TypeName(arg.Type, wr, arg.Origin));
              var n = dtor.EnclosingCtors.Count;
              if (n == 1) {
                wDtor.WriteLine("return _this.Get_().({0}).{1}", StructOfCtor(dtor.EnclosingCtors[0]), DatatypeFieldName(arg));
              } else {
                wDtor = wDtor.NewBlock("switch data := _this.Get_().(type)");
                var compiledConstructorsProcessed = 0;
                for (var i = 0; i < n; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.GetOrCreateCompileName(currentIdGenerator) == dtor.CorrespondingFormals[i].GetOrCreateCompileName(currentIdGenerator));
                  if (ctor_i.IsGhost) {
                    continue;
                  }
                  if (compiledConstructorsProcessed < compiledConstructorCount - 1) {
                    wDtor.WriteLine("case {0}: return data.{1}", StructOfCtor(ctor_i), DatatypeFieldName(arg));
                  } else {
                    wDtor.WriteLine("default: return data.({0}).{1}", StructOfCtor(ctor_i), DatatypeFieldName(arg));
                  }
                  compiledConstructorsProcessed++;
                }
              }
            }
          }
        }
      }

      {
        // String() method
        wr.WriteLine();
        var w = wr.NewNamedBlock("func (_this {0}) String() string", name);
        // TODO Avoid switch if only one branch
        var needData = dt is IndDatatypeDecl && dt.Ctors.Exists(ctor => !ctor.IsGhost && ctor.Formals.Exists(arg => !arg.IsGhost));
        w = w.NewNamedBlock("switch {0}_this.Get_().(type)", needData ? "data := " : "");
        w.WriteLine("case nil: return \"null\"");
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          var wCase = w.NewNamedBlock("case {0}:", StructOfCtor(ctor));
          var nm = (dt.EnclosingModuleDefinition.TryToAvoidName ? "" : dt.EnclosingModuleDefinition.Name + ".") + dt.Name + "." + ctor.Name;
          if (dt is CoDatatypeDecl) {
            wCase.WriteLine("return \"{0}\"", nm);
          } else {
            wCase.Write("return \"{0}\"", nm);
            var sep = " + \"(\" + ";
            var anyFormals = false;
            var k = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                anyFormals = true;
                if (UnicodeCharEnabled && arg.Type.IsStringType) {
                  wCase.Write($"{sep}data.{DatatypeFieldName(arg, k)}.VerbatimString(true)");
                } else {
                  wCase.Write($"{sep}{HelperModulePrefix}String(data.{DatatypeFieldName(arg, k)})");
                }

                sep = " + \", \" + ";
                k++;
              }
            }
            if (anyFormals) {
              wCase.Write(" + \")\"");
            }
            wCase.WriteLine();
          }
        }
        var wDefault = w.NewBlock("default:");
        if (dt is CoDatatypeDecl) {
          wDefault.WriteLine("return \"{0}.{1}.unexpected\"", dt.EnclosingModuleDefinition.GetCompileName(Options), dt.GetCompileName(Options));
        } else {
          wDefault.WriteLine("return \"<unexpected>\"");
        }
      }

      // Equals method
      {
        wr.WriteLine();
        var wEquals = wr.NewNamedBlock("func (_this {0}) Equals(other {0}) bool", name);
        // TODO: Way to implement shortcut check for address equality?
        var needData1 = dt.Ctors.Exists(ctor => !ctor.IsGhost && ctor.Formals.Exists(arg => !arg.IsGhost));

        wEquals = wEquals.NewNamedBlock("switch {0}_this.Get_().(type)", needData1 ? "data1 := " : "");
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          var wCase = wEquals.NewNamedBlock("case {0}:", StructOfCtor(ctor));

          var needData2 = ctor.Formals.Exists(arg => !arg.IsGhost);

          wCase.WriteLine("{0}, ok := other.Get_().({1})", needData2 ? "data2" : "_", StructOfCtor(ctor));
          wCase.Write("return ok");
          var k = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              wCase.Write(" && ");
              string nm = DatatypeFieldName(arg, k);
              var eqType = DatatypeWrapperEraser.SimplifyType(Options, arg.Type);
              if (IsDirectlyComparable(eqType)) {
                wCase.Write("data1.{0} == data2.{0}", nm);
              } else if (IsOrderedByCmp(eqType)) {
                wCase.Write("data1.{0}.Cmp(data2.{0}) == 0", nm);
              } else if (IsComparedByEquals(eqType)) {
                wCase.Write("data1.{0}.Equals(data2.{0})", nm);
              } else {
                wCase.Write("{0}AreEqual(data1.{1}, data2.{1})", HelperModulePrefix, nm);
              }
              k++;
            }
          }
          wCase.WriteLine();
        }
        var wDefault = wEquals.NewNamedBlock("default:");
        wDefault.WriteLine("return false; // unexpected");

        wr.WriteLine();
        var wEqualsGeneric = wr.NewNamedBlock("func (_this {0}) EqualsGeneric(other interface{{}}) bool", name);
        wEqualsGeneric.WriteLine("typed, ok := other.({0})", name);
        wEqualsGeneric.WriteLine("return ok && _this.Equals(typed)");
      }

      // RTD
      {
        var usedOrAutoInitTypeParams = UsedTypeParameters(dt, true);
        CreateRTD(name, usedOrAutoInitTypeParams, out var wDefault, wr);
        WriteRuntimeTypeDescriptorsLocals(usedOrAutoInitTypeParams, wDefault);

        var usedTypeParams = UsedTypeParameters(dt);
        var sep = typeDescriptorUses.Length != 0 && usedTypeParams.Count != 0 ? ", " : "";
        var arguments = usedTypeParams.Comma(tp => DefaultValue(new UserDefinedType(tp), wDefault, dt.Origin, true));
        wDefault.WriteLine($"return {TypeName_Companion(dt, wr, dt.Origin)}.Default({typeDescriptorUses}{sep}{arguments});");
      }

      EmitParentTraits(dt.Origin, name, false, dt.Traits, wr);

      return new ClassWriter(this, dt, false, name, dt.IsExtern(Options, out _, out _), null,
        wr, wr, wr, wr, staticFieldWriter, staticFieldInitWriter);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = CreateClass(nt, false, null, nt.TypeArgs,
        nt.ParentTypeInformation.UniqueParentTraits(), null, wr, includeRtd: false, includeEquals: false, includeString: true);
      var w = cw.ConcreteMethodWriter;
      var nativeType = nt.NativeType != null ? GetNativeTypeName(nt.NativeType) : null;
      if (nt.NativeType != null) {
        var intType = $"{HelperModulePrefix}Int";
        var wIntegerRangeBody = w.NewNamedBlock($"func (_this *{FormatCompanionTypeName(IdName(nt))}) IntegerRange(lo {intType}, hi {intType}) {HelperModulePrefix}Iterator");
        wIntegerRangeBody.WriteLine($"iter := {HelperModulePrefix}IntegerRange(lo, hi)");
        var wIterFuncBody = wIntegerRangeBody.NewBlock($"return func() ({AnyType}, bool)");
        wIterFuncBody.WriteLine("next, ok := iter()");
        wIterFuncBody.WriteLine("if !ok {{ return {0}(0), false }}", nativeType);
        wIterFuncBody.WriteLine($"return next.({intType}).{Capitalize(nativeType)}(), true");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var retType = nativeType ?? TypeName(nt.BaseType, w, nt.Origin);
        var wWitness = w.NewNamedBlock("func (_this *{0}) Witness() {1}", FormatCompanionTypeName(IdName(nt)), retType);
        var wStmts = wWitness.Fork();
        wWitness.Write("return ");
        if (nt.NativeType == null) {
          wWitness.Append(Expr(nt.Witness, false, wStmts));
          wWitness.WriteLine();
        } else {
          TrParenExpr(nt.Witness, wWitness, false, wStmts);
          wWitness.WriteLine(".{0}()", Capitalize(GetNativeTypeName(nt.NativeType)));
        }
      }

      var udt = UserDefinedType.FromTopLevelDecl(nt.Origin, nt);
      // RTD
      {
        CreateRTD(IdName(nt), nt.TypeArgs, out var wDefaultBody, wr);
        WriteRuntimeTypeDescriptorsLocals(nt.TypeArgs, wDefaultBody);
        var d = DefaultValue(udt, wr, nt.Origin, true);
        wDefaultBody.WriteLine("return {0}", d);
      }

      GenerateIsMethod(nt, wr);

      if (nt.Traits.Count != 0) {
        cw.InstanceFieldWriter.WriteLine($"_value {TypeName(udt, cw.InstanceFieldWriter, nt.Origin)}");
      }

      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = CreateClass(sst, false, null, sst.TypeArgs, null, null, wr, includeRtd: false, includeEquals: false, includeString: true);
      var w = cw.ConcreteMethodWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        var wStmts = w.Fork();
        witness.Append(Expr(sst.Witness, false, wStmts));
        DeclareField("Witness", false, true, true, sst.Rhs, sst.Origin, witness.ToString(), cw.ClassName, cw.StaticFieldWriter, cw.StaticFieldInitWriter, cw.ConcreteMethodWriter);
      }
      // RTD
      {
        CreateRTD(IdName(sst), sst.TypeArgs, out var wDefaultBody, wr);
        WriteRuntimeTypeDescriptorsLocals(sst.TypeArgs, wDefaultBody);
        var udt = UserDefinedType.FromTopLevelDecl(sst.Origin, sst);
        var d = DefaultValue(udt, wr, sst.Origin, true);
        wDefaultBody.WriteLine("return {0}", d);
      }

      GenerateIsMethod(sst, wr);
    }

    private void CreateRTD(string typeName, List<TypeParameter> usedParams, out ConcreteSyntaxTree wDefaultBody, ConcreteSyntaxTree wr) {
      Contract.Requires(typeName != null);
      Contract.Requires(usedParams != null);
      Contract.Requires(wr != null);
      Contract.Ensures(Contract.ValueAtReturn(out wDefaultBody) != null);

      wr.WriteLine();
      wr.Write($"func {FormatRTDName(typeName)}(");
      WriteRuntimeTypeDescriptorsFormals(usedParams, true, out var wrFormals, out _);
      wr.Append(wrFormals);
      var wTypeMethod = wr.NewBlock($") {DafnyTypeDescriptor}");
      wTypeMethod.WriteLine($"return type_{typeName}_{{{usedParams.Comma(tp => FormatRTDName(tp.GetCompileName(Options)))}}}");

      wr.WriteLine();
      var wType = wr.NewNamedBlock($"type type_{typeName}_ struct");
      WriteRuntimeTypeDescriptorsFields(usedParams, true, wType, null, null);

      wr.WriteLine();
      wDefaultBody = wr.NewNamedBlock("func (_this type_{0}_) Default() interface{{}}", typeName);

      wr.WriteLine();
      var wString = wr.NewNamedBlock($"func (_this type_{typeName}_) String() string");
      wString.WriteLine($"return \"{ModuleName}.{typeName}\"");
    }

    void GenerateIsMethod(RedirectingTypeDecl declWithConstraints, ConcreteSyntaxTree wr) {
      Contract.Requires(declWithConstraints is SubsetTypeDecl or NewtypeDecl);

      if (declWithConstraints.ConstraintIsCompilable) {
        var type = UserDefinedType.FromTopLevelDecl(declWithConstraints.Tok, (TopLevelDecl)declWithConstraints);

        wr.Write($"func (_this *{FormatCompanionTypeName(IdName((TopLevelDecl)declWithConstraints))}) Is_(");

        var count = WriteRuntimeTypeDescriptorsFormals(declWithConstraints.TypeArgs, false, out var wrFormals, out _);
        if (count != 0) {
          wr.Write($"{wrFormals}, ");
        }

        var sourceFormal = new Formal(declWithConstraints.Tok, "_source", type, true, false, null);
        var typeName = TypeName(type, wr, declWithConstraints.Tok);
        var wrBody = wr.NewBlock($"{IdName(sourceFormal)} {typeName}) bool");
        GenerateIsMethodBody(declWithConstraints, sourceFormal, wrBody);
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "uint8";
          break;
        case NativeType.Selection.SByte:
          name = "int8";
          break;
        case NativeType.Selection.UShort:
          name = "uint16";
          break;
        case NativeType.Selection.Short:
          name = "int16";
          break;
        case NativeType.Selection.UInt:
          name = "uint32";
          break;
        case NativeType.Selection.Int:
          name = "int32";
          break;
        case NativeType.Selection.ULong:
          name = "uint64";
          break;
        case NativeType.Selection.Long:
          name = "int64";
          break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new Cce.UnreachableException();  // to please the compiler
      }
    }
    protected class ClassWriter : IClassWriter {
      public readonly GoCodeGenerator CodeGenerator;
      public readonly TopLevelDecl ClassContext;
      public readonly bool IsClass;
      public readonly string ClassName;
      public readonly bool IsExtern;
      public readonly ConcreteSyntaxTree/*?*/ AbstractMethodWriter, ConcreteMethodWriter, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter;
      public bool AnyInstanceFields { get; private set; } = false;

      public ClassWriter(GoCodeGenerator codeGenerator, TopLevelDecl classContext, bool isClass, string className, bool isExtern, ConcreteSyntaxTree abstractMethodWriter, ConcreteSyntaxTree concreteMethodWriter,
        ConcreteSyntaxTree/*?*/ instanceFieldWriter, ConcreteSyntaxTree/*?*/ instanceFieldInitWriter, ConcreteSyntaxTree/*?*/ traitInitWriter,
        ConcreteSyntaxTree staticFieldWriter, ConcreteSyntaxTree staticFieldInitWriter) {
        Contract.Requires(codeGenerator != null);
        Contract.Requires(className != null);
        this.CodeGenerator = codeGenerator;
        this.ClassContext = classContext;
        this.IsClass = isClass;
        this.ClassName = className;
        this.IsExtern = isExtern;
        this.AbstractMethodWriter = abstractMethodWriter;
        this.ConcreteMethodWriter = concreteMethodWriter;
        this.InstanceFieldWriter = instanceFieldWriter;
        this.InstanceFieldInitWriter = instanceFieldInitWriter;
        this.TraitInitWriter = traitInitWriter;
        this.StaticFieldWriter = staticFieldWriter;
        this.StaticFieldInitWriter = staticFieldInitWriter;
      }

      public ConcreteSyntaxTree FieldWriter(bool isStatic) {
        return isStatic ? StaticFieldWriter : InstanceFieldWriter;
      }

      public ConcreteSyntaxTree FieldInitWriter(bool isStatic) {
        return isStatic ? StaticFieldInitWriter : InstanceFieldInitWriter;
      }

      public ConcreteSyntaxTree/*?*/ CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return CodeGenerator.CreateMethod(m, typeArgs, createBody, ClassContext, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.Origin, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return CodeGenerator.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, ClassContext, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance, lookasideBody);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IOrigin tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance) {
        return CodeGenerator.CreateGetter(name, resultType, tok, isStatic, createBody, member, ClassContext, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IOrigin tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return CodeGenerator.CreateGetterSetter(name, resultType, tok, createBody, member, ClassContext, ClassName, out setterWriter, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance);
      }
      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IOrigin tok, string rhs, Field field) {
        // FIXME: This should probably be done in Compiler.DeclareField().
        // Should just have these delegate methods take the ClassWriter as an
        // argument.
        if (!isStatic) {
          AnyInstanceFields = true;
        }
        CodeGenerator.DeclareField(name, IsExtern, isStatic, isConst, type, tok, rhs, ClassName, FieldWriter(isStatic), FieldInitWriter(isStatic), ConcreteMethodWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        var tok = field.Origin;
        var lvalue = CodeGenerator.EmitMemberSelect(w => w.Write("_this"), UserDefinedType.FromTopLevelDecl(tok, enclosingClass), field,
          [], enclosingClass.ParentFormalTypeParametersToActuals, instantiatedFieldType);
        var wRHS = lvalue.EmitWrite(FieldInitWriter(false));
        CodeGenerator.EmitCoercionIfNecessary(instantiatedFieldType, field.Type, tok, wRHS);
        wRHS.Write(CodeGenerator.PlaceboValue(instantiatedFieldType, ErrorWriter(), tok));
      }

      public ConcreteSyntaxTree/*?*/ ErrorWriter() => ConcreteMethodWriter;

      public void Finish() {
        CodeGenerator.FinishClass(this);
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
      TopLevelDecl ownerContext, string ownerName,
      ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance, bool lookasideBody) {
      var overriddenIns = m.EnclosingClass is TraitDecl && !forBodyInheritance ? null : m.OverriddenMethod?.Original.Ins;
      var overriddenOuts = m.EnclosingClass is TraitDecl && !forBodyInheritance ? null : m.OverriddenMethod?.Original.Outs;
      return CreateSubroutine(IdName(m), typeArgs, m.Ins, m.Outs, null,
        overriddenIns, overriddenOuts, null,
        m.Origin, m.IsStatic, createBody, ownerContext, ownerName, m, abstractWriter, concreteWriter, forBodyInheritance, lookasideBody);
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType,
      IOrigin tok, bool isStatic, bool createBody, MemberDecl member, TopLevelDecl ownerContext, string ownerName,
      ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance, bool lookasideBody) {

      var fnOverridden = (member as Function)?.OverriddenFunction?.Original;
      return CreateSubroutine(name, typeArgs, formals, [], resultType,
        fnOverridden?.Ins, fnOverridden == null ? null : [], fnOverridden?.ResultType,
        tok, isStatic, createBody, ownerContext, ownerName, member, abstractWriter, concreteWriter, forBodyInheritance, lookasideBody);
    }

    private ConcreteSyntaxTree CreateSubroutine(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> inParams, List<Formal> outParams, Type/*?*/ resultType,
      List<Formal>/*?*/ overriddenInParams, List<Formal>/*?*/ overriddenOutParams, Type/*?*/ overriddenResultType,
      IOrigin tok, bool isStatic, bool createBody, TopLevelDecl ownerContext, string ownerName, MemberDecl/*?*/ member,
      ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter,
      bool forBodyInheritance, bool lookasideBody) {
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(overriddenInParams == null || overriddenInParams.Count == inParams.Count);
      Contract.Requires(overriddenOutParams == null || overriddenOutParams.Count == outParams.Count);
      Contract.Requires(tok != null);
      Contract.Requires(ownerName != null);
      Contract.Requires(abstractWriter != null || concreteWriter != null);

      var customReceiver = createBody && !forBodyInheritance && member != null && NeedsCustomReceiver(member);
      ConcreteSyntaxTree wr;
      if (createBody || abstractWriter == null) {
        wr = concreteWriter;
        string receiver = isStatic || customReceiver ? FormatCompanionTypeName(ownerName) : ownerName;
        if (member != null && ownerContext is DatatypeDecl) {
          wr.Write("func ({0} {1}) ", isStatic || customReceiver ? "_static" : "_this", receiver);
        } else {
          wr.Write("func ({0} *{1}) ", isStatic || customReceiver ? "_static" : "_this", receiver);
        }
      } else {
        wr = abstractWriter;
      }
      wr.Write("{0}(", name);
      var prefix = "";
      var nTypes = WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, lookasideBody), wr, ref prefix, tp => $"{FormatRTDName(tp.GetCompileName(Options))} {DafnyTypeDescriptor}");
      if (customReceiver) {
        wr.Write("{0}_this {1}", nTypes != 0 ? ", " : "", TypeName(UserDefinedType.FromTopLevelDecl(tok, member.EnclosingClass), wr, tok));
      }
      var _ = WriteFormals(nTypes != 0 || customReceiver ? ", " : "", overriddenInParams ?? inParams, wr, inParams);
      wr.Write(")");

      // TODO: Maybe consider using named result parameters, since they're actually close to how Dafny method outs work
      if (overriddenOutParams != null) {
        WriteOutTypes(overriddenOutParams, overriddenResultType, wr, tok);
      } else {
        WriteOutTypes(outParams, resultType, wr, tok);
      }

      if (createBody) {
        var w = wr.NewBlock("");
        // Go doesn't have type parameters. Instead, the empty interface type is used as the type of what would have been type parameters.
        // If this is a routine inherited from a trait, then the Dafny signature of the method may have replaced the trait's type parameters.
        // Go has no direct support for this idiom. Instead, we re-declare the in-parameters with the actual type, let the re-declarations
        // shadow the given (generic) in-parameters, and then do a cast on entry to the body.
        // If the routine only contains a call to an inherited body, then we omit the conversions here.
        if (forBodyInheritance) {
          // don't do any conversions
        } else if (thisContext != null) {
          w = w.NewBlock("", open: BlockStyle.Brace);
          for (var i = 0; i < inParams.Count; i++) {
            var p = (overriddenInParams ?? inParams)[i];
            var instantiatedType = p.Type.Subst(thisContext.ParentFormalTypeParametersToActuals);
            if (!p.IsGhost && !instantiatedType.Equals(p.Type)) {
              // var p instantiatedType = p.(instantiatedType)
              var pName = IdName(inParams[i]);
              DeclareLocalVar(pName, instantiatedType, p.Origin, true, null, w);
              var wRhs = EmitAssignmentRhs(w);
              wRhs = EmitCoercionIfNecessary(p.Type, instantiatedType, p.Origin, wRhs);
              wRhs.Write(pName);
              EmitDummyVariableUse(pName, w);
            }
          }
        } else {
          Contract.Assert(overriddenInParams == null);
        }
        if (outParams.Any() && !forBodyInheritance) {
          var beforeReturn = w.Fork(0);
          EmitReturnWithCoercions(outParams, overriddenOutParams, thisContext?.ParentFormalTypeParametersToActuals, w);
          return beforeReturn;
        }
        return w;
      } else {
        wr.WriteLine();
        return null;
      }
    }

    protected void WriteOutTypes(List<Formal> outParams, Type/*?*/ resultType, ConcreteSyntaxTree wr, IOrigin tok) {
      var outTypes = new List<Type>();
      if (resultType != null) {
        outTypes.Add(resultType);
      }

      foreach (Formal f in outParams) {
        if (!f.IsGhost) {
          outTypes.Add(f.Type);
        }
      }
      if (outTypes.Count > 0) {
        wr.Write(' ');
        if (outTypes.Count > 1) {
          wr.Write('(');
        }
        wr.Write(Util.Comma(outTypes, ty => TypeName(ty, wr, tok)));
        if (outTypes.Count > 1) {
          wr.Write(')');
        }
      }
    }

    int WriteRuntimeTypeDescriptorsFields(List<TypeParameter> typeParams, bool useAllTypeArgs, ConcreteSyntaxTree/*?*/ wr, ConcreteSyntaxTree/*?*/ wInit, ConcreteSyntaxTree/*?*/ wParams) {
      Contract.Requires(typeParams != null);

      var count = 0;
      var sep = "";
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          var name = FormatRTDName(tp.GetCompileName(Options));
          wr?.WriteLine($"{name} {DafnyTypeDescriptor}");
          wInit?.WriteLine("_this.{0} = {0}", name);
          wParams?.Write($"{sep}{name} {DafnyTypeDescriptor}");
          sep = ", ";
          count++;
        }
      }
      return count;
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs,
      out ConcreteSyntaxTree wrFormals, out ConcreteSyntaxTree wrActuals) {
      Contract.Requires(typeParams != null);

      wrFormals = new ConcreteSyntaxTree();
      wrActuals = new ConcreteSyntaxTree();
      var count = 0;
      var prefix = "";
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          var parameterName = FormatRTDName(tp.GetCompileName(Options));
          wrFormals.Write($"{prefix}{parameterName} {DafnyTypeDescriptor}");
          wrActuals.Write($"{prefix}{parameterName}");
          prefix = ", ";
          count++;
        }
      }
      return count;
    }

    void WriteRuntimeTypeDescriptorsLocals(List<TypeParameter> typeParams, ConcreteSyntaxTree wr) {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      foreach (var tp in typeParams) {
        wr.WriteLine("{0} := _this.{0}", FormatRTDName(tp.GetCompileName(Options)));
        EmitDummyVariableUse(FormatRTDName(tp.GetCompileName(Options)), wr);
      }
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      if (cl is DatatypeDecl) {
        needsTypeParameter = false;
        needsTypeDescriptor = true;
      } else if (cl is TraitDecl) {
        needsTypeParameter = false;
        needsTypeDescriptor = isStatic || lookasideBody;
      } else {
        Contract.Assert(cl is ClassDecl);
        needsTypeParameter = false;
        needsTypeDescriptor = isStatic;
      }
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      var xType = DatatypeWrapperEraser.SimplifyTypeAndTrimSubsetTypes(Options, type);
      if (xType is BoolType) {
        return "_dafny.BoolType";
      } else if (xType is CharType) {
        return CharTypeDescriptorName;
      } else if (xType is IntType) {
        return "_dafny.IntType";
      } else if (xType is BigOrdinalType) {
        return "_dafny.IntType";
      } else if (xType is RealType) {
        return "_dafny.RealType";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        if (t.NativeType != null) {
          return string.Format("_dafny.{0}Type", Capitalize(GetNativeTypeName(t.NativeType)));
        } else {
          return "_dafny.IntType";
        }
      } else if (xType is SetType) {
        return "_dafny.SetType";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSetType";
      } else if (xType is SeqType) {
        return "_dafny.SeqType";
      } else if (xType is MapType) {
        return "_dafny.MapType";
      } else if (xType.IsRefType) {
        return string.Format("_dafny.CreateStandardTypeDescriptor({0})", TypeInitializationValue(xType, wr, tok, false, true));
      } else if (xType.IsArrayType) {
        return "_dafny.ArrayType";
      } else if (xType.IsTypeParameter) {
        var tp = type.AsTypeParameter;
        Contract.Assert(tp != null);
        string th;
        if (thisContext != null && tp.Parent is TopLevelDeclWithMembers and not TraitDecl) {
          th = "_this.";
        } else {
          th = "";
        }
        return string.Format("{0}{1}", th, FormatRTDName(tp.GetCompileName(Options)));
      } else if (xType.IsBuiltinArrowType) {
        return string.Format("_dafny.CreateStandardTypeDescriptor({0})", TypeInitializationValue(xType, wr, tok, false, true));
      } else if (xType is UserDefinedType udt) {
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);

        var w = new ConcreteSyntaxTree();
        w.Write("{0}(", cl is TupleTypeDecl ? "_dafny.TupleType" : TypeName_RTD(xType, w, tok));
        var typeArgs = cl is DatatypeDecl dt ? UsedTypeParameters(dt, udt.TypeArgs, true) : TypeArgumentInstantiation.ListFromClass(cl, udt.TypeArgs);
        EmitTypeDescriptorsActuals(typeArgs, udt.Origin, w, true);
        w.Write(")");
        return w.ToString();

      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected type
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, Type resultType, IOrigin tok, bool isStatic, bool createBody,
      MemberDecl/*?*/ member, TopLevelDecl ownerContext, string ownerName,
      ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance) {
      return CreateFunction(name, [], [], resultType,
        tok, isStatic, createBody, member, ownerContext, ownerName, abstractWriter, concreteWriter, forBodyInheritance, false);
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IOrigin tok, bool createBody,
      MemberDecl/*?*/ member, TopLevelDecl ownerContext, string ownerName,
      out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance) {

      var getterWriter = CreateGetter(name, resultType, tok, false, createBody, member, ownerContext, ownerName, abstractWriter, concreteWriter, forBodyInheritance);

      var valueParam = new Formal(tok, "value", resultType, true, false, null);
      setterWriter = CreateSubroutine(name + "_set_", [], [valueParam], [], null,
        [valueParam], [], null,
        tok, false, createBody, ownerContext, ownerName, member,
        abstractWriter, concreteWriter, forBodyInheritance, false);
      return getterWriter;
    }

    protected override bool SupportsStaticsInGenericClasses => false;
    protected override bool TraitRepeatsInheritedDeclarations => true;

    private void FinishClass(GoCodeGenerator.ClassWriter cw) {
      // Go gets weird about zero-length structs.  In particular, it likes to
      // make all pointers to a zero-length struct the same.  Irritatingly, this
      // forces us to waste space here.
      if (cw.IsClass && !cw.AnyInstanceFields) {
        cw.InstanceFieldWriter.WriteLine("dummy byte");
      }
    }

    protected override ConcreteSyntaxTree EmitNullTest(bool testIsNull, ConcreteSyntaxTree wr) {
      if (!testIsNull) {
        wr.Write("!");
      }
      wr.Write("_dafny.IsDafnyNull");
      return wr.ForkInParens();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START");
      wr.WriteLine("TAIL_CALL_START:");
      return wr;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START");
    }

    private const string AnyType = "interface{}"; // In Go 1.18, this type can be written as "any"

    private string CharTypeName => $"_dafny.{CharTypeNameProper}";
    private string CharTypeDescriptorName => $"_dafny.{CharTypeNameProper}Type";
    private string CharTypeNameProper => UnicodeCharEnabled ? "CodePoint" : "Char";

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(Options, type);
      if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return CharTypeName;
      } else if (xType is IntType) {
        return $"{HelperModulePrefix}Int";
      } else if (xType is BigOrdinalType) {
        return "_dafny.Ord";
      } else if (xType is RealType) {
        return "_dafny.Real";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "_dafny.BV";
      } else if (xType.AsNewtype != null && member == null) {  // when member is given, use UserDefinedType case below
        var newtypeDecl = xType.AsNewtype;
        if (newtypeDecl.NativeType is { } nativeType) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(newtypeDecl.ConcreteBaseType(xType.TypeArgs), wr, tok);
      } else if (xType.IsObjectQ) {
        return AnyType;
      } else if (xType.IsArrayType) {
        return "_dafny.Array";
      } else if (xType is UserDefinedType udt) {
        var s = FullTypeName(udt, member);
        var cl = udt.ResolvedClass;
        if (xType is ArrowType at) {
          return string.Format("func ({0}) {1}", Util.Comma(at.Args, arg => TypeName(arg, wr, tok)), TypeName(at.Result, wr, tok));
        } else if (udt.IsTypeParameter) {
          return AnyType;
        } else if (cl is TupleTypeDecl tupleTypeDecl) {
          return HelperModulePrefix + "Tuple";
        }
        if (udt.IsTraitType && udt.ResolvedClass.IsExtern(Options, out _, out _)) {
          // To use an external interface, we need to have values of the
          // interface type, so we treat an extern trait as a plain interface
          // value, not a pointer (a Go interface value is basically a typed
          // pointer anyway).
          //
          // Also don't use IdProtect so that we can have it be a built-in
          // name like error.
          return s;
        } else if (udt.IsDatatype || udt.IsTraitType) {
          // Don't return a pointer to the datatype because the datatype is
          // already represented using a pointer
          return IdProtect(s);
        } else {
          return "*" + IdProtect(s);
        }
      } else if (xType is SetType) {
        return HelperModulePrefix + "Set";
      } else if (xType is SeqType) {
        return HelperModulePrefix + "Sequence";
      } else if (xType is MultiSetType) {
        return HelperModulePrefix + "MultiSet";
      } else if (xType is MapType) {
        return "_dafny.Map";
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      // When returning nil, explicitly cast the nil so that type assertions work
      string nil() {
        return string.Format("({0})(nil)", TypeName(type, wr, tok));
      }

      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return $"{CharTypeName}({CharType.DefaultValueAsString})";
      } else if (xType is IntType or BigOrdinalType) {
        return "_dafny.Zero";
      } else if (xType is RealType) {
        return "_dafny.ZeroReal";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "_dafny.Zero";
      } else if (xType is SetType) {
        return "_dafny.EmptySet";
      } else if (xType is MultiSetType) {
        return "_dafny.EmptyMultiSet";
      } else if (xType is SeqType seq) {
        if (seq.Arg.IsCharType && !UnicodeCharEnabled) {
          return "_dafny.EmptySeq.SetString()";
        }
        return "_dafny.EmptySeq";
      } else if (xType is MapType) {
        return "_dafny.EmptyMap";
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter tp) {
        if (usePlaceboValue && !tp.Characteristics.HasCompiledValue) {
          return nil();
        } else if (constructTypeParameterDefaultsFromTypeDescriptors) {
          var w = new ConcreteSyntaxTree();
          w = EmitCoercionIfNecessary(from: null, to: xType, tok: tok, wr: w);
          w.Write(TypeDescriptor(udt, wr, udt.Origin));
          w.Write(".Default()");
          return w.ToString();
        } else {
          return FormatDefaultTypeParameterValue(tp);
        }
      } else if (cl is AbstractTypeDecl opaque) {
        return FormatDefaultTypeParameterValue(opaque);
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_Companion(cl, wr, tok) + ".Witness()";
        } else if (td.NativeType != null) {
          return GetNativeTypeName(td.NativeType) + "(0)";
        } else {
          return TypeInitializationValue(td.ConcreteBaseType(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return TypeName_Companion(cl, wr, tok) + ".Witness()";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return nil();
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("func ({0}) {1} {{ return {2}; }}", Util.Comma(udt.TypeArgs.GetRange(0, udt.TypeArgs.Count - 1), tp => TypeName(tp, wr, tok)), TypeName(udt.TypeArgs.Last(), wr, tok), rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            // non-null array type; we know how to initialize them
            return string.Format("_dafny.NewArrayWithValue(nil, {0})", Util.Comma(arrayClass.Dims, d => string.Format("_dafny.IntOf(0)")));
          } else {
            return nil();
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ClassLikeDecl or ArrowTypeDecl) {
        return nil();
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(Options, dt, out var innerType)) {
          var typeSubstMap = TypeParameter.SubstitutionMap(dt.TypeArgs, udt.TypeArgs);
          return TypeInitializationValue(innerType.Subst(typeSubstMap), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
        // In an auto-init context (like a field initializer), we may not have
        // access to all the type descriptors, so we can't construct the
        // default value, but then an empty structure is an acceptable default, since
        // Dafny proves the value won't be accessed.
        if (usePlaceboValue) {
          return string.Format("{0}{{}}", TypeName(udt, wr, tok));
        }
        var n = dt is TupleTypeDecl ? "_dafny.TupleOf" : $"{TypeName_Companion(dt, wr, tok)}.Default";
        var wTypeDescriptorArguments = new ConcreteSyntaxTree();
        var sep = "";
        WriteTypeDescriptors(dt, udt.TypeArgs, wTypeDescriptorArguments, ref sep);
        var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs);
        if (relevantTypeArgs.Count == 0) {
          sep = "";
        }
        var arguments = relevantTypeArgs.Comma(ta => DefaultValue(ta.Actual, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors));
        return $"{n}({wTypeDescriptorArguments}{sep}{arguments})";
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IOrigin tok, bool omitTypeArguments) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = "*" + IdProtect(fullCompileName);
      return s;
    }

    protected static string FormatCompanionName(string clsName) =>
      string.Format("Companion_{0}_", clsName);
    protected static string FormatCompanionTypeName(string clsName) =>
      // Need to export this because it could be for a trait that could be
      // derived from in another module
      string.Format("CompanionStruct_{0}_", clsName);
    protected static string FormatDatatypeConstructorName(string ctorName) =>
      string.Format("Create_{0}_", ctorName);
    protected static string FormatDatatypeConstructorCheckName(string ctorName) =>
      string.Format("Is_{0}", ctorName);
    protected static string FormatDatatypeDestructorName(string dtorName) =>
      string.Format("Dtor_{0}", dtorName);
    protected static string FormatDatatypeInterfaceName(string typeName) =>
      string.Format("Data_{0}_", typeName);
    protected static string FormatDefaultName(string typeName) =>
      string.Format("Default_{0}_", typeName);
    protected static string FormatInitializerName(string clsName) =>
      string.Format("New_{0}_", clsName);
    protected static string FormatLazyConstructorName(string datatypeName) =>
      string.Format("Lazy_{0}_", datatypeName);
    protected static string FormatLazyInterfaceName(string traitName) =>
      string.Format("Iface_{0}_", traitName);
    protected static string FormatRTDName(string formalName) =>
      string.Format("Type_{0}_", formalName);

    protected string TypeName_Related(Func<string, string> formatter, Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member = null) {
      Contract.Requires(formatter != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      // FIXME This is a hacky bit of string munging.

      string name = ClassName(type, wr, tok, member);
      string prefix, baseName;
      var periodIx = name.LastIndexOf('.');
      if (periodIx >= 0) {
        prefix = name.Substring(0, periodIx + 1);
        baseName = name.Substring(periodIx + 1);
      } else {
        prefix = "";
        baseName = name;
      }

      return prefix + formatter(baseName);
    }

    protected string TypeName_Constructor(DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      var ptr = ctor.EnclosingDatatype is CoDatatypeDecl ? "*" : "";
      return string.Format("{0}{1}_{2}", ptr, TypeName(UserDefinedType.FromTopLevelDecl(ctor.Origin, ctor.EnclosingDatatype), wr, ctor.Origin), ctor.GetCompileName(Options));
    }

    internal override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      // XXX This duplicates some of the logic in UserDefinedTypeName, but if we
      // don't do it here, we end up passing the name of the module to
      // FormatCompanionName, which doesn't help anyone
      if (type is UserDefinedType { ResolvedClass: not null } udt && IsExternMemberOfExternModule(member, udt.ResolvedClass)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!udt.ResolvedClass.EnclosingModuleDefinition.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(ModuleImports[udt.ResolvedClass.EnclosingModuleDefinition].Name);
      }
      return TypeName_Related(FormatCompanionName, type, wr, tok, member);
    }

    protected string TypeName_CompanionType(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      return TypeName_Related(FormatCompanionTypeName, type, wr, tok);
    }

    protected string TypeName_Initializer(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      return TypeName_Related(FormatInitializerName, type, wr, tok);
    }

    protected string TypeName_RTD(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      return TypeName_Related(FormatRTDName, type, wr, tok);
    }

    protected string ClassName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member = null) {
      return type is UserDefinedType udt ? FullTypeName(udt, member) : TypeName(type, wr, tok, member);
    }

    protected string UnqualifiedClassName(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      return type is UserDefinedType udt ? UnqualifiedTypeName(udt) : TypeName(type, wr, tok);
    }

    protected string DatatypeFieldName(Formal formal, int formalNonGhostIndex) {
      // Don't rely on base.FormalName because it needlessly (for us) passes the
      // value through IdProtect when we're going to capitalize it
      return formal.HasName ? Capitalize(formal.CompileName) : "A" + formalNonGhostIndex + "_";
    }

    protected string DatatypeFieldName(Formal formal) {
      Contract.Assert(formal.HasName);
      return Capitalize(formal.CompileName);
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isExtern, bool isStatic, bool isConst, Type type, IOrigin tok, string/*?*/ rhs, string className, ConcreteSyntaxTree wr, ConcreteSyntaxTree initWriter, ConcreteSyntaxTree concreteMethodWriter) {
      if (isExtern) {
        Error(GeneratorErrors.ErrorId.c_Go_unsupported_field, tok, wr, "Unsupported field {0} in extern trait", name);
      }

      if (isConst && rhs != null) {
        var receiver = isStatic ? FormatCompanionTypeName(className) : className;
        var wBody = concreteMethodWriter.NewNamedBlock("func (_this *{0}) {1}() {2}", receiver, name, TypeName(type, concreteMethodWriter, tok));
        wBody.WriteLine("return {0}", rhs);
      } else {
        wr.WriteLine("{0} {1}", name, TypeName(type, initWriter, tok));

        if (isStatic) {
          initWriter.WriteLine("{0}: {1},", name, rhs ?? PlaceboValue(type, initWriter, tok));
        } else if (rhs != null) {
          initWriter.WriteLine("_this.{0} = {1}", name, rhs);
        }
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IOrigin tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write("{0}{1} {2}", prefix, name, TypeName(type, wr, tok));
        return true;
      } else {
        return false;
      }
    }

    private ConcreteSyntaxTree/*?*/ DeclareLocalVar(string name, Type/*?*/ type, IOrigin/*?*/ tok, bool includeRhs, bool leaveRoomForRhs, ConcreteSyntaxTree wr) {
      wr.Write("var {0}", name);

      if (type != null) {
        // Always specify the type in case the rhs is nil
        wr.Write(" {0}", TypeName(type, wr, tok));
      }

      ConcreteSyntaxTree w;
      if (includeRhs) {
        if (!leaveRoomForRhs) {
          wr.Write(" = ");
        }
        w = wr.Fork();
      } else {
        w = null;
      }

      if (!leaveRoomForRhs) {
        wr.WriteLine();
        EmitDummyVariableUse(name, wr);
      }

      return w;
    }

    protected override void EmitDummyVariableUse(string variableName, ConcreteSyntaxTree wr) {
      Contract.Requires(variableName != null);
      Contract.Requires(wr != null);

      wr.WriteLine("_ = {0}", variableName);
    }

    protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
      var w = DeclareLocalVar(name, type, tok, includeRhs: (rhs != null || leaveRoomForRhs), leaveRoomForRhs: leaveRoomForRhs, wr: wr);
      if (rhs != null) {
        w.Write(rhs);
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, IOrigin/*?*/ tok, ConcreteSyntaxTree wr) {
      return DeclareLocalVar(name, type, tok, includeRhs: true, leaveRoomForRhs: false, wr: wr);
    }

    protected override bool UseReturnStyleOuts(MethodOrConstructor m, int nonGhostOutCount) => true;

    protected override bool NeedsCastFromTypeParameter => true;
    protected override bool SupportsMultipleReturns => true;
    protected override string StmtTerminator => "";

    protected override void DeclareLocalOutVar(string name, Type type, IOrigin tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IOrigin tok, ConcreteSyntaxTree wr) {
      // emit nothing; this is only for actual parametric polymorphism, not RTDs
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitMultiAssignment(List<Expression> lhsExprs, List<ILvalue> wLhss, List<Type> lhsTypes, out List<ConcreteSyntaxTree> wRhss, List<Type> rhsTypes, ConcreteSyntaxTree wr) {
      // TODO Go actually supports multi-assignment, but that will only work
      // in the simple (but very typical) case where an lvalue represents an
      // actual lvalue that is written via an assignment statement.  (Actually,
      // currently *all* Go lvalues work this way, but in the future we could
      // implement getters and setters via ILvalueWriter.)
      //
      // Given a way to inquire whether a given lvalue is an actual lvalue in
      // the target, we could implement multi-assignment for the special case
      // where all lvalues are real lvalues.
      base.EmitMultiAssignment(lhsExprs, wLhss, lhsTypes, out wRhss, rhsTypes, wr);
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var isString = DatatypeWrapperEraser.SimplifyTypeAndTrimNewtypes(Options, arg.Type).IsStringType;
      var wStmts = wr.Fork();
      if (isString && UnicodeCharEnabled) {
        wr.Write("_dafny.Print(");
        wr.Append(Expr(arg, false, wStmts));
        wr.WriteLine(".VerbatimString(false))");
      } else if (!isString ||
                 (arg.Resolved is MemberSelectExpr mse &&
                  mse.Member.IsExtern(Options, out _, out _))) {
        wr.Write("_dafny.Print(");
        wr.Append(Expr(arg, false, wStmts));
        wr.WriteLine(")");
      } else {
        wr.Write("_dafny.Print((");
        wr.Append(Expr(arg, false, wStmts));
        wr.Write(")");
        if (!UnicodeCharEnabled) {
          wr.Write(".SetString()");
        }
        wr.WriteLine(")");
      }
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      EmitReturnWithCoercions(outParams, null, null, wr);
    }

    protected void EmitReturnWithCoercions(List<Formal> outParams, List<Formal>/*?*/ overriddenOutParams, Dictionary<TypeParameter, Type>/*?*/ typeMap, ConcreteSyntaxTree wr) {
      wr.Write("return");
      var sep = " ";
      for (var i = 0; i < outParams.Count; i++) {
        var f = outParams[i];
        if (!f.IsGhost) {
          wr.Write(sep);
          ConcreteSyntaxTree wOutParam;
          if (overriddenOutParams == null && typeMap != null) {
            wOutParam = EmitCoercionIfNecessary(f.Type.Subst(typeMap), f.Type, f.Origin, wr);
          } else if (overriddenOutParams != null) {
            // ignore typeMap
            wOutParam = EmitCoercionIfNecessary(f.Type, overriddenOutParams[i].Type, f.Origin, wr);
          } else {
            wOutParam = wr;
          }
          wOutParam.Write(IdName(f));
          sep = ", ";
        }
      }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var wBody = wr.NewBlock(open: BlockStyle.Brace);
      var w = wBody.Fork();
      var prefix = createContinueLabel ? "C" : "L";
      wBody.WriteLine($"goto {prefix}{label};");
      wr.Fork(-1).WriteLine($"{prefix}{label}:");
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, ConcreteSyntaxTree wr) {
      if (label == null) {
        wr.WriteLine("break");
      } else {
        wr.WriteLine("goto L{0}", label);
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine("goto C{0};", label);
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      wr.WriteLine("_yielded <- struct{}{}");
      wr.WriteLine("_, _ok = <- _cont");
      wr.WriteLine("if !_ok { return }");
    }

    protected override void EmitAbsurd(string/*?*/ message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("panic(\"{0}\")", message);
    }

    protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("panic(");
      if (tok != null) {
        wr.Write("\"" + tok.OriginToString(Options) + ": \" + ");
      }

      TrParenExpr(messageExpr, wr, false, wStmts);
      if (UnicodeCharEnabled && messageExpr.Type.IsStringType) {
        wr.Write(".VerbatimString(false))");
      } else {
        wr.WriteLine(".String())");
      }
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      wr.Write("for ");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlock("");
      return wBody;
    }

    protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp,
      string/*?*/ endVarName,
      List<Statement> body, List<Label> labels, ConcreteSyntaxTree wr) {

      wr.Write($"for {loopIndex.GetOrCreateCompileName(currentIdGenerator)} := ");
      var startWr = wr.Fork();
      wr.Write($"; ");

      ConcreteSyntaxTree bodyWr;
      if (goingUp) {
        if (endVarName == null) {
          wr.Write("true");
        } else if (IsOrderedByCmp(loopIndex.Type)) {
          wr.Write($"{loopIndex.GetOrCreateCompileName(currentIdGenerator)}.Cmp({endVarName}) < 0");
        } else {
          wr.Write($"{loopIndex.GetOrCreateCompileName(currentIdGenerator)} < {endVarName}");
        }
        if (AsNativeType(loopIndex.Type) == null) {
          bodyWr = wr.NewBlock($"; {loopIndex.GetOrCreateCompileName(currentIdGenerator)} = {loopIndex.GetOrCreateCompileName(currentIdGenerator)}.Plus(_dafny.One)");
        } else {
          bodyWr = wr.NewBlock($"; {loopIndex.GetOrCreateCompileName(currentIdGenerator)}++");
        }
      } else {
        if (endVarName == null) {
          wr.Write("true");
        } else if (IsOrderedByCmp(loopIndex.Type)) {
          wr.Write($"{endVarName}.Cmp({loopIndex.GetOrCreateCompileName(currentIdGenerator)}) < 0");
        } else {
          wr.Write($"{endVarName} < {loopIndex.GetOrCreateCompileName(currentIdGenerator)}");
        }
        bodyWr = wr.NewBlock($"; ");
        if (AsNativeType(loopIndex.Type) == null) {
          bodyWr.WriteLine($"{loopIndex.GetOrCreateCompileName(currentIdGenerator)} = {loopIndex.GetOrCreateCompileName(currentIdGenerator)}.Minus(_dafny.One)");
        } else {
          bodyWr.WriteLine($"{loopIndex.GetOrCreateCompileName(currentIdGenerator)}--");
        }
      }
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> boundAction, ConcreteSyntaxTree wr, string start = null) {
      start = start ?? "0";
      var boundWriter = new ConcreteSyntaxTree();
      boundAction(boundWriter);
      var bound = boundWriter.ToString();
      return wr.NewNamedBlock("for {0} := {2}; {0} < {1}; {0}++", indexVar, bound, start);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for {0} := {1}IntOf({2}); ; {0} = {0}.Times(_dafny.Two)", indexVar, HelperModulePrefix, start);
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} = {0}.Plus(_dafny.One)", varName);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} = {0}.Minus(_dafny.One)", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return "_dafny.Quantifier";
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {

      var okVar = idGenerator.FreshId("_ok");
      var iterVar = idGenerator.FreshId("_iter");
      wr.Write("for {0} := _dafny.Iterate(", iterVar);
      collectionWriter = wr.Fork();
      var wBody = wr.NewBlock(");;");
      wBody.WriteLine("{0}, {1} := {2}()", tmpVarName, okVar, iterVar);
      wBody.WriteLine("if !{0} {{ break }}", okVar);
      return wBody;
    }

    [CanBeNull]
    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
      var conditions = new List<string> { };
      if (boundVarType.IsNonNullRefType) {
        conditions.Add($"!_dafny.IsDafnyNull({tmpVarName})");
      }

      if (boundVarType.IsRefType) {
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          // Nothing more to test
        } else if (boundVarType.IsTraitType) {
          var trait = boundVarType.AsTraitType;
          conditions.Add(
            $"{HelperModulePrefix}InstanceOfTrait/*1*/({tmpVarName}.(_dafny.TraitOffspring), {TypeName_Companion(trait, wPreconditions, tok)}.TraitID_)");
        } else {
          var typeAssertSucceeds = idGenerator.FreshId("_typeAssertSucceeds");
          wPreconditions.WriteLine(
            $@"{typeAssertSucceeds} := func(param interface{{}}) bool {{ var ok bool; _, ok = param.({TypeName(boundVarType, wPreconditions, tok)}); return ok}}");
          conditions.Add($"{typeAssertSucceeds}({tmpVarName})");
        }
      }

      if (!conditions.Any()) {
        conditions.Add("true");
      }

      var typeTest = string.Join("&&", conditions);
      if (boundVarType.IsRefType && !boundVarType.IsNonNullRefType && typeTest != "true") {
        typeTest = $"_dafny.IsDafnyNull({tmpVarName}) || " + typeTest;
      }

      typeTest = typeTest == "true" ? null : typeTest;
      return typeTest == null ? null : wr => wr.Write(typeTest);
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {

      if (introduceBoundVar) {
        wr.WriteLine("var {0} {1}", boundVarName, TypeName(boundVarType, wr, tok));
      }

      var wrAssign = wr;
      if (boundVarType.IsRefType && !boundVarType.IsNonNullRefType) {
        var wIf = EmitIf($"_dafny.IsDafnyNull({tmpVarName})", true, wr);
        wIf.WriteLine("{0} = ({1})(nil)", boundVarName, TypeName(boundVarType, wr, tok));
        wrAssign = wr.NewBlock("", open: BlockStyle.Brace);
      }

      var cast = $".({TypeName(boundVarType, wrAssign, tok)})";
      tmpVarName = $"interface{{}}({tmpVarName})";
      wrAssign.WriteLine("{0} = {1}{2}", boundVarName, tmpVarName, cast);
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      var okVar = idGenerator.FreshId("_ok");
      var iterVar = idGenerator.FreshId("_iter");
      wr.Write("for {0} := _dafny.Iterate(", iterVar);
      collectionWriter = wr.Fork();
      var wBody = wr.NewBlock(");;");
      wBody.WriteLine("{0}, {1} := {2}()", boundVarName, okVar, iterVar);
      wBody.WriteLine("if !{0} {{ break }}", okVar);
      return wBody;
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall /*?*/, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TraitDecl { IsObjectTrait: true }) {
        wr.Write("_dafny.New_Object()");
      } else {
        var ctor = (Constructor)initCall?.Method; // correctness of cast follows from precondition of "EmitNew"
        var sep = "";
        wr.Write("{0}(", TypeName_Initializer(type, wr, tok));
        EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, wr);
        wr.Write(ConstructorArguments(initCall, wStmts, ctor, sep));
        wr.Write(")");
      }
    }

    protected override bool DeterminesArrayTypeFromExampleElement => true;

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {

      string sep;
      if (mustInitialize) {
        var initValue = DefaultValue(elementType, wr, tok, true);
        wr.Write("_dafny.NewArrayWithValue({0}", initValue);
        sep = ", ";
      } else if (exampleElement != null) {
        wr.Write("_dafny.NewArrayFromExample({0}, nil", exampleElement);
        sep = ", ";
      } else {
        wr.Write("_dafny.NewArray(");
        sep = "";
      }

      foreach (var dim in dimensions) {
        wr.Write($"{sep}{dim}");
        sep = ", ";
      }

      wr.Write(")");
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write("{0}", TypeName_Companion(((UserDefinedType)e.Type).ResolvedClass, wr, e.Origin));
      } else if (e.Value == null) {
        wr.Write("({0})(nil)", TypeName(e.Type, wr, e.Origin));
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr chrLit) {
        TrCharLiteral(chrLit, wr);
      } else if (e is StringLiteralExpr strLit) {
        TrStringLiteral(strLit, wr);
      } else if (AsNativeType(e.Type) is NativeType nt) {
        wr.Write("{0}({1})", GetNativeTypeName(nt), (BigInteger)e.Value);
      } else if (e.Value is BigInteger i) {
        EmitIntegerLiteral(i, wr);
      } else if (e.Value is BaseTypes.BigDec n) {
        var zeros = Repeat("0", Math.Abs(n.Exponent));
        string str;
        if (n.Exponent >= 0) {
          str = n.Mantissa + zeros;
        } else {
          str = n.Mantissa + "/1" + zeros;
        }
        wr.Write("_dafny.RealOfString(\"{0}\")", str);
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected literal
      }
    }
    void EmitIntegerLiteral(BigInteger i, ConcreteSyntaxTree wr) {
      Contract.Requires(wr != null);
      if (i.IsZero) {
        wr.Write($"{HelperModulePrefix}Zero");
      } else if (i.IsOne) {
        wr.Write($"{HelperModulePrefix}One");
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write($"{HelperModulePrefix}IntOfInt64({i})");
      } else {
        wr.Write($"{HelperModulePrefix}IntOfString(\"{i}\")");
      }
    }

    protected void TrCharLiteral(CharLiteralExpr chr, ConcreteSyntaxTree wr) {
      var v = (string)chr.Value;
      wr.Write($"{CharTypeName}(");
      // See comment in TrStringLiteral for why we can't just translate directly sometimes.
      if (!UnicodeCharEnabled && Util.MightContainNonAsciiCharacters(v, false)) {
        var c = Util.UnescapedCharacters(Options, v, false).Single();
        wr.Write($"{c}");
      } else {
        wr.Write("'{0}'", TranslateEscapes(v, isChar: true));
      }
      wr.Write(")");
    }

    protected override void TrStringLiteral(StringLiteralExpr str, ConcreteSyntaxTree wr) {
      Contract.Requires(str != null);
      Contract.Requires(wr != null);
      var s = (string)str.Value;
      if (UnicodeCharEnabled) {
        wr.Write($"_dafny.UnicodeSeqOfUtf8Bytes(");
        EmitStringLiteral(s, str.IsVerbatim, wr);
        wr.Write(")");
      } else {
        // When --unicode-char is false, it may not be possible to translate a Dafny string into a valid Go string,
        // since Go string literals have to be encodable in UTF-8,
        // but Dafny allows invalid sequences of surrogate characters.
        // In addition, _dafny.SeqOfString iterates over the runes in the Go string
        // rather than the equivalent UTF-16 code units.
        // That means in many cases we can't create a Dafny string value by emitting
        // _dafny.SeqOfString("..."), since there's no way to encode the right data in the Go string literal.
        // Instead, if any non-ascii characters might be present, just emit a sequence of the direct UTF-16 code units instead.
        if (Util.MightContainNonAsciiCharacters(s, false)) {
          wr.Write($"_dafny.SeqOfChars(");
          var comma = "";
          foreach (var c in Util.UnescapedCharacters(Options, s, str.IsVerbatim)) {
            wr.Write(comma);
            wr.Write($"{c}");
            comma = ", ";
          }

          wr.Write(")");
        } else {
          wr.Write($"{HelperModulePrefix}SeqOfString(");
          EmitStringLiteral(s, str.IsVerbatim, wr);
          wr.Write(")");
        }
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      var n = str.Length;
      if (!isVerbatim) {
        wr.Write("\"{0}\"", TranslateEscapes(str, isChar: false));
      } else {
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
            wr.Write("\\\"");
            i++;
          } else if (str[i] == '\\') {
            wr.Write("\\\\");
          } else if (str[i] == '\n') {
            wr.Write("\\n");
          } else if (str[i] == '\r') {
            wr.Write("\\r");
          } else {
            wr.Write(str[i]);
          }
        }
        wr.Write("\"");
      }
    }

    private static string TranslateEscapes(string s, bool isChar) {
      if (isChar) {
        s = s.Replace("\\\"", "\"");
      } else {
        s = s.Replace("\\'", "'");
      }

      s = Util.ReplaceNullEscapesWithCharacterEscapes(s);

      s = Util.ExpandUnicodeEscapes(s, false);

      return s;
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {

      string literalSuffix = null;
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out _, out literalSuffix, out _);
      }

      if (nativeType == null) {
        wr.Write('(');
        var middle = wr.Fork();
        wr.Write($").Modulo(_dafny.One.Lsh({HelperModulePrefix}IntOf({bvType.Width})))");
        return middle;
      } else if (bvType.Width < nativeType.Bitwidth) {
        wr.Write("((");
        var middle = wr.Fork();
        // print in hex, because that looks nice
        wr.Write(") & 0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix);
        return middle;
      } else {
        // no truncation needed
        return wr;
      }
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out _, out _, out needsCast);
      }

      var bv = e0.Type.NormalizeToAncestorType().AsBitVectorType;
      if (bv.Width == 0) {
        tr(e0, wr, inLetExprBody, wStmts);
      } else {
        ConcreteSyntaxTree wFirstArg;
        if (bv.NativeType != null) {
          wr.Write("_dafny.{0}{1}(", isRotateLeft ? "Lrot" : "Rrot", Capitalize(GetNativeTypeName(bv.NativeType)));
          wFirstArg = wr.Fork();
          wr.Write(", ");
        } else {
          wr.Write('(');
          wFirstArg = wr.Fork();
          wr.Write(").{0}(", isRotateLeft ? "Lrot" : "Rrot");
        }
        wFirstArg.Append(Expr(e0, inLetExprBody, wStmts));
        wr.Append(Expr(e1, inLetExprBody, wStmts));
        wr.Write(", {0})", bv.Width);

        if (needsCast) {
          wr.Write(".Int64()");
        }
      }
    }

    protected override bool CompareZeroUsingSign(Type type) {
      return AsNativeType(type) == null;
    }

    protected override ConcreteSyntaxTree EmitSign(Type type, ConcreteSyntaxTree wr) {
      // This is only called when CompareZeroUsingSign returns true
      Contract.Assert(AsNativeType(type) == null);

      var w = wr.Fork();
      wr.Write(".Sign()");
      return w;
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("_dafny.NewBuilder()");
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("{0}.Add(_dafny.TupleOf(", ingredients);
      var wrTuple = wr.Fork();
      wr.WriteLine("))");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write("(*({0}).IndexInt({1}))", prefix, i);
    }

    protected override string IdName(TopLevelDecl d) {
      return IdName((Declaration)d);
    }

    protected override string IdName(MemberDecl member) {
      return IdName((Declaration)member);
    }

    private string IdName(Declaration decl) {
      if (HasCapitalizationConflict(decl)) {
        // Don't use Go_ because Capitalize might use it and we know there's a conflict
        return "Go__" + decl.GetCompileName(Options);
      } else {
        return IdProtect(Capitalize(decl.GetCompileName(Options)));
      }
    }

    protected override string PrefixForForcedCapitalization => "Go_";

    protected override string IdMemberName(MemberSelectExpr mse) {
      return Capitalize(mse.MemberName);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);

      switch (name) {
        // Keywords
        case "break":
        case "case":
        case "chan":
        case "const":
        case "continue":
        case "default":
        case "defer":
        case "else":
        case "fallthrough":
        case "for":
        case "func":
        case "go":
        case "goto":
        case "if":
        case "import":
        case "interface":
        case "map":
        case "package":
        case "range":
        case "return":
        case "select":
        case "struct":
        case "switch":
        case "type":
        case "var":

        // Built-in functions
        case "append":
        case "cap":
        case "close":
        case "complex":
        case "copy":
        case "delete":
        case "imag":
        case "len":
        case "make":
        case "new":
        case "panic":
        case "print":
        case "println":
        case "real":
        case "recover":

        case "String":
        case "Equals":
        case "EqualsGeneric":
        case "Default":

        // Built-in types (can also be used as functions)
        case "bool":
        case "byte":
        case "complex64":
        case "complex128":
        case "error":
        case "float32":
        case "float64":
        case "int":
        case "int8":
        case "int16":
        case "int32":
        case "int64":
        case "rune":
        case "string":
        case "uint":
        case "uint8":
        case "uint16":
        case "uint32":
        case "uint64":
        case "uintptr":
          return name + "_";
        default:
          return name;
      }
    }

    /* Obtained by running the following on the console on the page https://pkg.go.dev/std :
     var lineLength = 0; copy([...document.querySelectorAll(
    "td > div.UnitDirectories-pathCell > div > span, "+
    "td > div.UnitDirectories-pathCell > div > a")]
    .map((e, i) => {
        var res = JSON.stringify(e.textContent);
        if(lineLength + res.length > 94) {
            lineLength = res.length;
            res = ",\n      " + res;
        } else if(i > 0) {
            res = "," + res;
            lineLength += res.length;
        }
        return res;
    }).join(""))
     */
    public readonly HashSet<string> ReservedModuleNames = [
      "c",
      "archive",
      "bufio",
      "builtin",
      "bytes",
      "cmp",
      "compress",
      "container",
      "context",
      "crypto",
      "database",
      "debug",
      "embed",
      "encoding",
      "errors",
      "expvar",
      "flag",
      "fmt",
      "go",
      "hash",
      "html",
      "image",
      "index",
      "internal",
      "io",
      "log",
      "maps",
      "math",
      "mime",
      "net",
      "os",
      "path",
      "plugin",
      "reflect",
      "regexp",
      "runtime",
      "slices",
      "sort",
      "strconv",
      "strings",
      "sync",
      "syscall",
      "testing",
      "text",
      "time",
      "unicode",
      "unsafe"
    ];

    public string PublicModuleIdProtect(string name) {
      if (ReservedModuleNames.Contains(name.ToLower())) {
        return "_" + name;
      } else {
        return IdProtect(name);
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      return UserDefinedTypeName(udt, full: true, member: member);
    }

    private string UnqualifiedTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      return UserDefinedTypeName(udt, full: false, member: member);
    }

    private string UserDefinedTypeName(UserDefinedType udt, bool full, MemberDecl/*?*/ member = null) {
      Contract.Requires(udt != null);
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.GetCompileName(Options));
      } else {
        return UserDefinedTypeName(cl, full, member);
      }
    }

    private string UserDefinedTypeName(TopLevelDecl cl, bool full, MemberDecl/*?*/ member = null) {
      string enclosingModuleDefinitionId;
      if (CurrentModule == cl.EnclosingModuleDefinition || cl.EnclosingModuleDefinition.IsDefaultModule) {
        enclosingModuleDefinitionId = PublicModuleIdProtect(cl.EnclosingModuleDefinition.GetCompileName(Options));
      } else {
        enclosingModuleDefinitionId = ModuleImports[cl.EnclosingModuleDefinition].Name;
      }
      if (IsExternMemberOfExternModule(member, cl)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.EnclosingModuleDefinition.IsDefaultModule);  // default module is not marked ":extern"
        return enclosingModuleDefinitionId;
      } else {
        if (cl.IsExtern(Options, out var qual, out _)) {
          // No need to take into account the second argument to extern, since
          // it'll already be cl.CompileName
          if (qual == null) {
            if (this.ModuleName == enclosingModuleDefinitionId) {
              qual = "";
            } else {
              qual = enclosingModuleDefinitionId;
            }
          }
          // Don't use IdName since that'll capitalize, which is unhelpful for
          // built-in types
          return qual + (qual == "" ? "" : ".") + cl.GetCompileName(Options);
        } else if (!full || cl.EnclosingModuleDefinition.TryToAvoidName || this.ModuleName == enclosingModuleDefinitionId) {
          return IdName(cl);
        } else {
          return enclosingModuleDefinitionId + "." + IdName(cl);
        }
      }
    }

    private bool IsExternMemberOfExternModule(MemberDecl/*?*/ member, TopLevelDecl cl) {
      return cl is DefaultClassDecl && Attributes.Contains(cl.EnclosingModuleDefinition.Attributes, "extern") &&
             member != null && member.IsExtern(Options, out _, out _);
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      wr.Write("_this");
    }

    protected override void EmitNull(Type type, ConcreteSyntaxTree wr) {
      if (type.IsIntegerType || type.IsBitVectorType || type.AsNewtype != null) {
        wr.Write("_dafny.NilInt");
      } else if (type.IsRealType) {
        wr.Write("_dafny.NilReal");
      } else {
        wr.Write("({0})(nil)", TypeName(type, wr, tok: null));
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("(func () {0} {{ if ", TypeName(resultType, wr, null));
      wr.Append(Expr(guard, inLetExprBody, wStmts));
      wr.Write(" { return ");
      var wBranch = EmitCoercionIfNecessary(thn.Type, resultType, thn.Origin, wr);
      wBranch.Append(Expr(thn, inLetExprBody, wStmts));
      wr.Write(" }; return ");
      wBranch = EmitCoercionIfNecessary(els.Type, resultType, thn.Origin, wr);
      wBranch.Append(Expr(els, inLetExprBody, wStmts));
      wr.Write(" })() ");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      EmitDatatypeValue(dtv.Ctor.EnclosingDatatype, dtv.Ctor, dtv.IsCoCall, typeDescriptorArguments, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      var ctorName = ctor.GetCompileName(Options);
      var companionName = TypeName_Companion(dt, wr, dt.Origin);

      var sep = typeDescriptorArguments.Length != 0 && arguments.Length != 0 ? ", " : "";
      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.TupleOf({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate: Companion_Dt_.CreateCtor(args)
        wr.Write($"{companionName}.{FormatDatatypeConstructorName(ctorName)}({typeDescriptorArguments}{sep}{arguments})");
      } else {
        // Co-recursive call
        // Generate:  Companion_Dt_.LazyDt(func () Dt => Companion_Dt_.CreateCtor(args))
        wr.Write("{0}.{1}({2}{3}func () {4} ", companionName, FormatLazyConstructorName(dt.GetCompileName(Options)),
          typeDescriptorArguments, sep,
          TypeName(UserDefinedType.FromTopLevelDecl(dt.Origin, dt), wr, dt.Origin));
        wr.Write("{{ return {0}.{1}({2}{3}{4}) }}", companionName, FormatDatatypeConstructorName(ctorName), typeDescriptorArguments, sep, arguments);
        wr.Write(')');
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          preString = "_dafny.ArrayLen(";
          postString = string.Format(", {0}){1}", idParam == null ? 0 : (int)idParam,
            id == SpecialField.ID.ArrayLengthInt ? ".Int()" : "");
          break;
        case SpecialField.ID.Floor:
          compiledName = "Int()";
          break;
        case SpecialField.ID.IsLimit:
          compiledName = "IsLimitOrd()";
          break;
        case SpecialField.ID.IsSucc:
          compiledName = "IsSuccOrd()";
          break;
        case SpecialField.ID.Offset:
          compiledName = "OrdOffset()";
          break;
        case SpecialField.ID.IsNat:
          compiledName = "IsNatOrd()";
          break;
        case SpecialField.ID.Keys:
          compiledName = "Keys()";
          break;
        case SpecialField.ID.Values:
          compiledName = "Values()";
          break;
        case SpecialField.ID.Items:
          compiledName = "Items()";
          break;
        case SpecialField.ID.Reads:
          compiledName = "_reads";
          break;
        case SpecialField.ID.Modifies:
          compiledName = "_modifies";
          break;
        case SpecialField.ID.New:
          compiledName = "_new";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string/*?*/ additionalCustomParameter = null, bool internalAccess = false) {
      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(Options, member);
      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        return SimpleLvalue(obj);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return SimpleLvalue(w => w.Write("true"));
      } else if (member is DatatypeDestructor dtor) {
        return SimpleLvalue(wr => {
          wr = EmitCoercionIfNecessary(dtor.Type, expectedType, Token.NoToken, wr);
          if (dtor.EnclosingClass is TupleTypeDecl) {
            Contract.Assert(dtor.CorrespondingFormals.Count == 1);
            var formal = dtor.CorrespondingFormals[0];
            wr.Write("(*(");
            obj(wr);
            wr.Write(").IndexInt({0}))", formal.NameForCompilation);
          } else {
            obj(wr);
            wr.Write(".{0}()", FormatDatatypeDestructorName(dtor.GetCompileName(Options)));
          }
        });
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        return SimpleLvalue(wr => {
          wr = EmitCoercionIfNecessary(sf.Type, expectedType, Token.NoToken, wr);
          obj(wr);
          GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
          if (compiledName.Length != 0) {
            wr.Write(".{0}", Capitalize(compiledName));
          } else {
            // this member selection is handled by some kind of enclosing function call, so nothing to do here
          }
        });
      } else if (member is DatatypeDiscriminator sf2 && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        // sf2 is needed here only because the scope rules for these pattern matches are asinine: sf is *still in scope* but it's useless because it may not have been assigned to!
        return SimpleLvalue(wr => {
          wr = EmitCoercionIfNecessary(sf2.Type, expectedType, Token.NoToken, wr);
          obj(wr);
          // FIXME This is a pretty awful string hack.
          wr.Write(".{0}()", FormatDatatypeConstructorCheckName(fieldName.Substring(3)));
        });
      } else if (member is Function fn) {
        typeArgs = typeArgs.Where(ta => NeedsTypeDescriptor(ta.Formal)).ToList();
        if (typeArgs.Count == 0 && additionalCustomParameter == null) {
          var lvalue = SuffixLvalue(obj, ".{0}", IdName(member));
          return CoercedLvalue(lvalue, fn.GetMemberType((ArrowTypeDecl)expectedType.AsArrowType.ResolvedClass), expectedType);
        } else {
          // We need an eta conversion to adjust for the difference in arity.
          // func (a0 T0, a1 T1, ...) ResultType { return obj.F(rtd0, rtd1, ..., a0, a1, ...); }
          // Start by writing to the suffix:  F(rtd0, rtd1, ...
          var suffixWr = new ConcreteSyntaxTree();
          suffixWr.Write(IdName(member));
          suffixWr.Write("(");
          var suffixSep = "";
          EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), fn.Origin, suffixWr, ref suffixSep);
          if (additionalCustomParameter != null) {
            suffixWr.Write("{0}{1}", suffixSep, additionalCustomParameter);
            suffixSep = ", ";
          }
          // Write the prefix and the rest of the suffix
          var prefixWr = new ConcreteSyntaxTree();
          var prefixSep = "";
          prefixWr.Write("func (");
          foreach (var arg in fn.Ins) {
            if (!arg.IsGhost) {
              var name = idGenerator.FreshId("_eta");
              var ty = arg.Type.Subst(typeMap);
              prefixWr.Write($"{prefixSep}{name} {TypeName(ty, prefixWr, arg.Origin)}");
              suffixWr.Write("{0}{1}", suffixSep, name);
              suffixSep = ", ";
              prefixSep = ", ";
            }
          }
          var resultType = fn.ResultType.Subst(typeMap);
          prefixWr.Write(") {0} {{ return ", TypeName(resultType, prefixWr, fn.Origin));
          suffixWr.Write(")");
          var suffix = suffixWr.ToString();
          return EnclosedLvalue(
            prefixWr.ToString(),
            wr => {
              var wCall = EmitCoercionIfNecessary(fn.ResultType, resultType, Token.NoToken, wr: wr);
              obj(wCall);
              wCall.Write(".");
              wCall.Write(suffix);
              wr.Write("; }");
            },
            "");
        }
      } else {
        var field = (Field)member;
        ILvalue lvalue;
        if (member.IsStatic) {
          lvalue = SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.Origin, member), IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.Origin, w);
            w.Write(")");
          });
        } else if (NeedsCustomReceiverNotTrait(member)) {
          // instance const in a newtype
          Contract.Assert(typeArgs.Count == 0);
          lvalue = SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.Origin, member), IdName(member));
            obj(w);
            w.Write(")");
          });
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          lvalue = SuffixLvalue(obj, $".{InternalFieldPrefix}{member.GetCompileName(Options)}");
        } else if (internalAccess) {
          lvalue = SuffixLvalue(obj, $".{IdName(member)}");
        } else if (member is ConstantField) {
          lvalue = SimpleLvalue(w => {
            obj(w);
            w.Write(".{0}(", IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.Origin, w);
            w.Write(")");
          });
        } else if (member.EnclosingClass is TraitDecl) {
          lvalue = GetterSetterLvalue(obj, IdName(member), $"{IdName(member)}_set_");
        } else {
          lvalue = SuffixLvalue(obj, $".{IdName(member)}");
        }
        return CoercedLvalue(lvalue, field.Type, expectedType);
      }
    }

    protected override string ArrayIndexToNativeInt(string s, Type type) {
      var nt = AsNativeType(type);
      if (nt == null) {
        return $"({s}).Int()";
      } else {
        return $"int({s})";
      }
    }

    protected override ConcreteSyntaxTree ExprToInt(Type fromType, ConcreteSyntaxTree wr) {
      if (AsNativeType(fromType) == null) {
        return wr;
      }
      wr.Write("_dafny.IntOfAny");
      return wr.ForkInParens();
    }

    /// <summary>
    /// Emit to "wr" a call
    ///     _dafny.ArrayGet( <<wArray>>, <<wArguments>> )        // if isGet
    /// or
    ///     _dafny.ArraySet( <<wArray>>, <<wArguments>> )        // if !isGet
    /// and return (wArray, wArguments). Optimize these calls based on "dimensionCount" and "elementType".
    /// "elementType" is allowed to be "null", which says to not specialize based on the element type.
    /// </summary>
    private (ConcreteSyntaxTree wArray, ConcreteSyntaxTree wArguments) CallArrayGetOrSet(bool isGet,
      int dimensionCount, [CanBeNull] Type elementType, ConcreteSyntaxTree wr) {

      var typeSpecialization = "";
      if (dimensionCount == 1 && elementType != null) {
        if (elementType.IsCharType) {
          typeSpecialization = CharTypeNameProper;
        } else {
          var nt = AsNativeType(elementType);
          if (nt != null && nt.Sel == NativeType.Selection.Byte) {
            typeSpecialization = "Byte";
          }
        }
      }
      if (isGet && typeSpecialization == "") {
        wr = EmitCoercionIfNecessary(null, elementType, Token.NoToken, wr);
      }

      ConcreteSyntaxTree wArray;
      if (dimensionCount != 1) {
        // use a general call, which uses a varargs for the indices
        wr.Write(isGet ? "_dafny.ArrayGet(" : "_dafny.ArraySet(");
        wArray = wr.Fork();
        wr.Write(", ");
      } else {
        // specialize to a call with exactly one index argument
        wArray = wr.ForkInParens();
        wr.Write($"{(isGet ? ".ArrayGet1" : ".ArraySet1")}{typeSpecialization}(");
      }
      var wArguments = wr.Fork();
      wr.Write(")");
      return (wArray, wArguments);
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      // Note, the indices are formulated in the native array-index type.
      var (wArray, wArguments) = CallArrayGetOrSet(true, indices.Count, elmtType, wr);
      for (int i = 0; i < indices.Count; i++) {
        if (i > 0) {
          wArguments.Write(", ");
        }
        indices[i](wArguments);
      }
      return wArray;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var (wArray, wArguments) = CallArrayGetOrSet(true, indices.Count, elmtType, wr);
      wArguments.Write(indices.Comma(index => {
        var idx = Expr(index, inLetExprBody, wStmts).ToString();
        return ArrayIndexToNativeInt(idx, index.Type);
      }));
      return wArray;
    }

    protected override (ConcreteSyntaxTree/*array*/, ConcreteSyntaxTree/*rhs*/) EmitArrayUpdate(List<Action<ConcreteSyntaxTree>> indices, Type elementType, ConcreteSyntaxTree wr) {
      var (wArray, wArguments) = CallArrayGetOrSet(false, indices.Count, elementType, wr);
      var wRhs = wArguments.Fork();
      for (int i = 0; i < indices.Count; i++) {
        wArguments.Write(", ");
        indices[i](wArguments);
      }
      return (wArray, wRhs);
    }

    protected override void EmitArrayIndexToInt(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wIndex) {
      wIndex = new ConcreteSyntaxTree();
      wr.Write($"{HelperModulePrefix}IntOf(");
      wr.Append(wIndex);
      wr.Write(")");
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (expr is LiteralExpr lit) {
        wr.Write(lit.Value.ToString());
      } else {
        TrParenExpr(expr, wr, inLetExprBody, wStmts);
        if (AsNativeType(expr.Type) == null) {
          wr.Write(".Int()");
        }
      }
    }

    // This will probably move up to the superclass once more compilers are using dafnyRuntime.dfy
    protected void TrExprToSizeT(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (expr is LiteralExpr lit) {
        wr.Write(lit.Value.ToString());
      } else {
        if (AsNativeType(expr.Type) == null) {
          TrParenExpr(expr, wr, inLetExprBody, wStmts);
          wr.Write(".Uint32()");
        } else {
          wr.Write("uint32(");
          wr.Append(Expr(expr, inLetExprBody, wStmts));
          wr.Write(")");
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var type = source.Type.NormalizeToAncestorType();
      if (type is SeqType seqType) {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Select(");
        TrExprToSizeT(index, inLetExprBody, wr, wStmts);
        wr.Write(").({0})", TypeName(seqType.Arg, wr, null));
      } else if (type is MultiSetType) {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Multiplicity(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")");
      } else {
        Contract.Assert(type is MapType);
        // map or imap
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Get(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(").({0})", TypeName(((MapType)type).Range, wr, null));
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (resultCollectionType.AsSeqType != null) {
        wr.Write($"{DafnySequenceCompanion}.Update(");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(", ");
        TrExprToSizeT(index, inLetExprBody, wr, wStmts);
        wr.Write(", ");
        wr.Append(CoercedExpr(value, resultCollectionType.ValueArg, inLetExprBody, wStmts));
        wr.Write(")");
      } else if (resultCollectionType.AsMapType is { } mapType) {
        EmitIndexCollectionUpdate(source.Type, out var wSource, out var wIndex, out var wValue, wr, false);
        TrParenExpr(source, wSource, inLetExprBody, wSource);
        wIndex.Append(CoercedExpr(index, mapType.Domain, inLetExprBody, wSource));
        wValue.Append(CoercedExpr(value, mapType.Range, inLetExprBody, wSource));
      } else {
        Contract.Assert(resultCollectionType.AsMultiSetType != null);
        EmitIndexCollectionUpdate(source.Type, out var wSource, out var wIndex, out var wValue, wr, false);
        TrParenExpr(source, wSource, inLetExprBody, wSource);
        wIndex.Append(CoercedExpr(index, resultCollectionType.Arg, inLetExprBody, wSource));
        wValue.Append(Expr(value, inLetExprBody, wSource));
      }
    }

    protected override void EmitIndexCollectionUpdate(Type sourceType, out ConcreteSyntaxTree wSource, out ConcreteSyntaxTree wIndex, out ConcreteSyntaxTree wValue, ConcreteSyntaxTree wr, bool nativeIndex) {
      if (sourceType.IsArrayType) {
        Contract.Assume(nativeIndex);
        (wSource, var wArguments) = CallArrayGetOrSet(false, 1, null, wr);
        wValue = wArguments.Fork();
        wArguments.Write(", ");
        wIndex = wArguments.Fork();
      } else {
        wSource = wr.ForkInParens();
        wr.Write(nativeIndex ? ".UpdateInt(" : ".Update(");
        wIndex = wr.Fork();
        wr.Write(", ");
        wValue = wr.Fork();
        wr.Write(")");
      }
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (fromArray) {
        wr.Write("_dafny.ArrayRangeToSeq(");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(", ");

        if (lo == null) {
          wr.Write("_dafny.NilInt");
        } else {
          TrExprToBigInt(lo, wr, inLetExprBody);
        }

        wr.Write(", ");

        if (hi == null) {
          wr.Write("_dafny.NilInt");
        } else {
          TrExprToBigInt(hi, wr, inLetExprBody);
        }

        wr.Write(")");
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);

        if (lo == null) {
          if (hi == null) {
            return;
          }

          wr.Write(".Take(");
          TrExprToSizeT(hi, inLetExprBody, wr, wStmts);
          wr.Write(")");
        } else {
          if (hi == null) {
            wr.Write(".Drop(");
            TrExprToSizeT(lo, inLetExprBody, wr, wStmts);
            wr.Write(")");
          } else {
            wr.Write(".Subsequence(");
            TrExprToSizeT(lo, inLetExprBody, wr, wStmts);
            wr.Write(", ");
            TrExprToSizeT(hi, inLetExprBody, wr, wStmts);
            wr.Write(")");
          }
        }
      }
    }

    void TrExprToBigInt(Expression e, ConcreteSyntaxTree wr, bool inLetExprBody) {
      var wStmts = wr.Fork();
      var nativeType = AsNativeType(e.Type);
      if (nativeType != null) {
        wr.Write(HelperModulePrefix);
        switch (nativeType.Sel) {
          case NativeType.Selection.Byte:
            wr.Write("IntOfUint8(");
            break;
          case NativeType.Selection.UShort:
            wr.Write("IntOfUint16(");
            break;
          case NativeType.Selection.UInt:
            wr.Write("IntOfUint32(");
            break;
          case NativeType.Selection.ULong:
            wr.Write("IntOfUint64(");
            break;
          case NativeType.Selection.SByte:
            wr.Write("IntOfInt8(");
            break;
          case NativeType.Selection.Short:
            wr.Write("IntOfInt16(");
            break;
          case NativeType.Selection.Int:
            wr.Write("IntOfInt32(");
            break;
          case NativeType.Selection.Long:
            wr.Write($"IntOfInt64(");
            break;
          default:
            throw new Cce.UnreachableException();  // unexpected nativeType.Selection value
        }
      }

      TrParenExpr(e, wr, inLetExprBody, wStmts);

      if (nativeType != null) {
        wr.Write(")");
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{HelperModulePrefix}SeqCreate(");
      TrExprToSizeT(expr.N, inLetExprBody, wr, wStmts);
      wr.Write(", ");
      var fromType = (ArrowType)expr.Initializer.Type.NormalizeExpand();
      var atd = (ArrowTypeDecl)fromType.ResolvedClass;
      var tParam = new UserDefinedType(expr.Origin,
        new TypeParameter(expr.Origin, new Name("X"), TPVarianceSyntax.NonVariant_Strict));
      var toType = new ArrowType(expr.Origin, atd, [Type.Int], tParam);
      var initWr = EmitCoercionIfNecessary(fromType, toType, expr.Origin, wr);
      initWr.Append(Expr(expr.Initializer, inLetExprBody, wStmts));
      wr.Write(")");
      if (fromType.Result.IsCharType && !UnicodeCharEnabled) {
        // Tag this sequence as being a string at runtime,
        // but only if --unicode-char is false.
        // See "Printing strings and characters" in docs/Compilation/StringsAndChars.md.
        wr.Write(".SetString()");
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var eeType = expr.E.Type.NormalizeToAncestorType();
      if (eeType is SeqType) {
        TrParenExpr("_dafny.MultiSetFromSeq", expr.E, wr, inLetExprBody, wStmts);
      } else if (eeType is SetType) {
        TrParenExpr("_dafny.MultiSetFromSet", expr.E, wr, inLetExprBody, wStmts);
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();
      }
    }

    protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function, List<Expression> arguments,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type type, IOrigin tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      Contract.Assert(boundVars.Count == boundTypes.Count);
      wr.Write("(func (");
      for (int i = 0; i < boundVars.Count; i++) {
        if (i > 0) {
          wr.Write(", ");
        }
        wr.Write("{0} {1}", boundVars[i], TypeName(boundTypes[i], wr, tok));
      }

      wr.Write(") {0}", TypeName(type, wr, tok));
      var wLambdaBody = wr.NewBigExprBlock("", ")");
      var w = EmitReturnExpr(wLambdaBody);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      wr.Write("{0}.{1}()", source, FormatDatatypeConstructorCheckName(ctor.GetCompileName(Options)));
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex,
      DatatypeCtor ctor, Func<List<Type>> getTypeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
        source(wr);
      } else if (ctor.EnclosingDatatype is TupleTypeDecl tupleTypeDecl) {
        Contract.Assert(tupleTypeDecl.NonGhostDims != 1); // such a tuple is an erasable-wrapper type, handled above
        wr.Write("(*(");
        source(wr);
        wr.Write(").IndexInt({0})).({1})", formalNonGhostIndex, TypeName(getTypeArgs()[formalNonGhostIndex], wr, Token.NoToken));
      } else {
        var dtorName = DatatypeFieldName(dtor, formalNonGhostIndex);
        wr = EmitCoercionIfNecessary(from: dtor.Type, to: bvType, tok: dtor.Origin, wr: wr);
        source(wr);
        wr.Write(".Get_().({0}).{1}", TypeName_Constructor(ctor, wr), dtorName);
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames,
      Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      wr.Write("func (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1} {2}", i == 0 ? "" : ", ", inNames[i], TypeName(inTypes[i], wr, tok));
      }
      var w = wr.NewExprBlock(") {0}", TypeName(resultType, wr, tok));
      return w;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IOrigin bvTok, Type bodyType, IOrigin bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      var w = wr.NewExprBlock("func ({0} {1}) {2}", bvName, TypeName(bvType, wr, bvTok), TypeName(bodyType, wr, bodyTok));
      wStmts = w.Fork();
      w.Write("return ");
      wrBody = w.Fork();
      w.WriteLine();
      wr.Write('(');
      wrRhs = wr.Fork();
      wr.Write(')');
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var w = wr.NewBigExprBlock("func () " + TypeName(resultType, wr, resultTok), "()");
      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var w = wr.NewExprBlock("func ({0} int) {1}", bvName, TypeName(resultType, wr, resultTok));
      wr.Write("({0})", source);
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            wr.Write("^ ");
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
          } else {
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
            wr.Write(".Not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.NormalizeToAncestorType().AsSeqType != null) {
            wr.Write($"{HelperModulePrefix}IntOfUint32(");
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
            wr.Write(".Cardinality())");
          } else {
            TrParenExpr(expr, wr, inLetExprBody, wStmts);
            wr.Write(".Cardinality()");
          }

          break;
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected unary expression
      }
    }

    private bool IsDirectlyComparable(Type t) {
      t = t.GetRuntimeType();
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null || t.IsArrayType ||
             t is UserDefinedType { ResolvedClass: ClassDecl };
    }

    private bool IsOrderedByCmp(Type t) {
      t = t.GetRuntimeType();
      return t.IsIntegerType || t.IsRealType || t.IsBigOrdinalType ||
             (t.AsBitVectorType is { NativeType: null }) ||
             (t.AsNewtype is { NativeType: null });
    }

    private bool IsComparedByEquals(Type t) {
      t = t.GetRuntimeType();
      return t.IsIndDatatype || t is CollectionType;
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Type e0Type, Type e1Type, IOrigin tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      out bool coerceE1,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;
      coerceE1 = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          if (AsNativeType(resultType) != null) {
            opString = "&";
          } else {
            callString = "And";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          if (AsNativeType(resultType) != null) {
            opString = "|";
          } else {
            callString = "Or";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          if (AsNativeType(resultType) != null) {
            opString = "^";
          } else {
            callString = "Xor";
          }
          break;

        case BinaryExpr.ResolvedOpcode.EqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(Options, e0Type);
            if (!EqualsUpToParameters(eqType, DatatypeWrapperEraser.SimplifyType(Options, e1Type))) {
              staticCallString = $"{HelperModulePrefix}AreEqual";
            } else if (IsOrderedByCmp(eqType)) {
              callString = "Cmp";
              postOpString = " == 0";
            } else if (IsComparedByEquals(eqType)) {
              callString = "Equals";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "==";
            } else {
              staticCallString = $"{HelperModulePrefix}AreEqual";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(Options, e0Type);
            if (!EqualsUpToParameters(eqType, DatatypeWrapperEraser.SimplifyType(Options, e1Type))) {
              preOpString = "!";
              staticCallString = $"{HelperModulePrefix}AreEqual";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "!=";
              postOpString = "/* dircomp */";
            } else if (IsOrderedByCmp(eqType)) {
              callString = "Cmp";
              postOpString = " != 0";
            } else if (IsComparedByEquals(eqType)) {
              preOpString = "!";
              callString = "Equals";
            } else {
              preOpString = "!";
              staticCallString = $"{HelperModulePrefix}AreEqual";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
          if (IsOrderedByCmp(e0Type)) {
            callString = "Cmp";
            postOpString = " < 0";
          } else {
            opString = "<";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Le:
          if (IsOrderedByCmp(e0Type)) {
            callString = "Cmp";
            postOpString = " <= 0";
          } else {
            opString = "<=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
          if (IsOrderedByCmp(e0Type)) {
            callString = "Cmp";
            postOpString = " >= 0";
          } else {
            opString = ">=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          if (IsOrderedByCmp(e0Type)) {
            callString = "Cmp";
            postOpString = " > 0";
          } else {
            opString = ">";
          }
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (resultType.NormalizeToAncestorType().IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "<<";
            if (AsNativeType(e1Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            if (AsNativeType(e1Type) != null) {
              callString = "Lsh(_dafny.IntOfUint64(uint64";
              postOpString = "))";
            } else {
              callString = "Lsh";
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (AsNativeType(resultType) != null) {
            opString = ">>";
            if (AsNativeType(e1Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            if (AsNativeType(e1Type) != null) {
              callString = "Rsh(_dafny.IntOfUint64(uint64";
              postOpString = "))";
            } else {
              callString = "Rsh";
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.NormalizeToAncestorType().IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null) {
            opString = "+";
          } else {
            callString = "Plus";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.NormalizeToAncestorType().IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            if (AsNativeType(resultType).LowerBound == BigInteger.Zero) {
              // Go is a PITA about subtracting unsigned integers---it complains
              // if they're constant and the substraction underflows.  Hiding
              // one of the arguments behind a thunk is kind of hideous but
              // it does prevent constant folding.
              opString = string.Format("- (func () {0} {{ return ", GetNativeTypeName(AsNativeType(resultType)));
              postOpString = " })()";
            } else {
              opString = "-";
            }
          } else if (resultType.IsCharType) {
            opString = "-";
          } else {
            callString = "Minus";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (resultType.NormalizeToAncestorType().IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "*";
          } else {
            callString = "Times";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              staticCallString = "_dafny.Div" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
            } else {
              // Native division is fine for unsigned
              opString = "/";
            }
          } else {
            callString = "DivBy";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.LowerBound < BigInteger.Zero) {
              // Want Euclidean division for signed types
              staticCallString = "_dafny.Mod" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
            } else {
              // Native division is fine for unsigned
              opString = "%";
            }
          } else {
            callString = "Modulo";
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "Equals"; break;
        case BinaryExpr.ResolvedOpcode.SeqEq:
          staticCallString = $"{DafnySequenceCompanion}.Equal"; break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "IsProperSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "IsSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = "IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          callString = "Merge"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersection"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          callString = "Subtract"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          staticCallString = $"{DafnySequenceCompanion}.IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          staticCallString = $"{DafnySequenceCompanion}.IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = $"{DafnySequenceCompanion}.Concatenate"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          staticCallString = $"{DafnySequenceCompanion}.Contains"; reverseArguments = true; break;

        default:
          base.CompileBinOp(op, e0Type, e1Type, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments, out truncateResult, out convertE1_to_int, out coerceE1,
            errorWr);
          break;
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("{0}.Cmp(_dafny.Zero) == 0", varName);
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (toType.Equals(fromType)) {
        TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Int) || fromType.NormalizeToAncestorType().IsBitVectorType || fromType.IsCharType || fromType.IsBigOrdinalType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(toType) == null);
          wr.Write("_dafny.RealOfFrac(");
          ConcreteSyntaxTree w;
          if (fromType.IsCharType) {
            wr.Write($"{HelperModulePrefix}IntOfInt32(rune");
            w = wr.Fork();
            wr.Write(")");
          } else if (AsNativeType(fromType) is NativeType nt) {
            wr.Write($"{HelperModulePrefix}IntOf{Capitalize(GetNativeTypeName(nt))}(");
            w = wr.Fork();
            wr.Write(")");
          } else {
            w = wr;
          }
          TrParenExpr(fromExpr, w, inLetExprBody, wStmts);
          wr.Write(", _dafny.One)");
        } else if (toType.IsCharType) {
          if (fromType.IsCharType) {
            EmitExpr(fromExpr, inLetExprBody, wr, wStmts);
          } else {
            wr.Write($"{CharTypeName}(");
            TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
            if (AsNativeType(fromType) == null) {
              wr.Write(".Int32()");
            }
            wr.Write(")");
          }
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(fromType);
          var toNative = AsNativeType(toType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            wr.Write(GetNativeTypeName(toNative));
            TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
          } else if (fromType.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write($"{HelperModulePrefix}IntOfInt32(rune(");
              wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
              wr.Write("))");
            } else {
              // char -> native
              wr.Write(GetNativeTypeName(toNative));
              TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
          } else if (fromNative != null) {
            Contract.Assert(toNative == null); // follows from other checks
            // native (int or bv) -> big-integer (int or bv)
            wr.Write($"{HelperModulePrefix}IntOf{Capitalize(GetNativeTypeName(fromNative))}(");
            wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
            wr.Write(')');
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(fromExpr);
            UnaryOpExpr u = fromExpr.Resolved as UnaryOpExpr;
            MemberSelectExpr m = fromExpr.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("{0}({1})", GetNativeTypeName(toNative), literal);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(u.E, wr, inLetExprBody, wStmts);
              wr.Write(u.E.Type.NormalizeToAncestorType().AsSeqType != null ? ".Cardinality())" : ".CardinalityInt())");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              wr.Write("{0}(_dafny.ArrayLenInt(", GetNativeTypeName(toNative));
              wr.Append(Expr(m.Obj, inLetExprBody, wStmts));
              wr.Write(", 0))");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
              wr.Write(".{0}()", Capitalize(GetNativeTypeName(toNative)));
            }
          }
        }
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(fromType) == null);
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(toType) == null);
          wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
        } else if (toType.IsCharType) {
          wr.Write($"{CharTypeName}(");
          TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
          wr.Write(".Int().Int32())");
        } else {
          // real -> (int or bv)
          TrParenExpr(fromExpr, wr, inLetExprBody, wStmts);
          wr.Write(".Int()");
          if (AsNativeType(toType) is NativeType nt) {
            wr.Write(".{0}()", Capitalize(GetNativeTypeName(nt)));
          }
        }
      } else if (fromType.Equals(toType) || fromType.AsNewtype != null || toType.AsNewtype != null) {
        wr.Append(Expr(fromExpr, inLetExprBody, wStmts));
      } else {
        wr = EmitCoercionIfNecessary(fromType, toType, fromExpr.Origin, wr);
        EmitExpr(fromExpr, inLetExprBody, wr, wStmts);
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IOrigin tok, ConcreteSyntaxTree wr) {
      if (fromType.IsRefType && !fromType.IsNonNullRefType) {
        Contract.Assert(toType.IsRefType);
        if (toType.IsNonNullRefType) {
          wr.Write($"!_dafny.IsDafnyNull({localName}) && ");
        } else {
          wr.Write($"_dafny.IsDafnyNull({localName}) || ");
        }
      }

      if (fromType.IsSubtypeOf(toType, true, true)) {
        wr.Write("true");
      } else if (toType.IsTraitType) {
        wr.Write($"{HelperModulePrefix}InstanceOfTrait({localName}.(_dafny.TraitOffspring), {TypeName_Companion(toType.AsTraitType, wr, tok)}.TraitID_)");
      } else if (toType.IsRefType) {
        wr.Write($"{HelperModulePrefix}InstanceOf({localName}, ({TypeName(toType, wr, tok)})(nil))");
      } else if (fromType.IsTraitType && toType.AsNewtype != null) {
        wr.Write($"{HelperModulePrefix}InstanceOf({localName}, (*{ClassName(toType, wr, tok)})(nil))");
      } else {
        wr.Write($"{HelperModulePrefix}InstanceOf({localName}, {TypeName(toType, wr, tok)}{{}})");
      }
    }

    protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(".IsInteger() && ");
    }

    protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("_dafny.IsCodePoint");
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(" && ");
    }

    protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitLiteralExpr(wr, new LiteralExpr(source.Origin, lo) { Type = Type.Int });
      wr.Write(".Cmp(");
      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(") <= 0 && ");

      EmitExpr(source, false, wr.ForkInParens(), wStmts);
      wr.Write(".Cmp(");
      EmitLiteralExpr(wr, new LiteralExpr(source.Origin, hi) { Type = Type.Int });
      wr.Write(") < 0 && ");
    }

    private static bool EqualsUpToParameters(Type type1, Type type2) {
      // TODO Consider whether Type.SameHead should return true in this case
      return Type.SameHead(type1, type2) || (type1.IsArrayType && type1.IsArrayType);
    }

    protected override ConcreteSyntaxTree FromFatPointer(Type type, ConcreteSyntaxTree wr) {
      if (type.HasFatPointer) {
        var w = wr.ForkInParens();
        wr.Write("._value");
        return w;
      } else {
        return wr;
      }
    }

    protected override ConcreteSyntaxTree ToFatPointer(Type type, ConcreteSyntaxTree wr) {
      if (type.HasFatPointer) {
        wr.Write(TypeName_Initializer(type, wr, type.AsNewtype.Origin));
        return wr.ForkInParens();
      } else {
        return wr;
      }
    }

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, IOrigin tok, ConcreteSyntaxTree wr, Type toOrig = null) {
      if (toOrig != null) {
        to = toOrig;
      }

      if (to == null) {
        return wr;
      }

      if (from != null && from.IsTraitType && to.AsNewtype != null) {
        wr = FromFatPointer(to, wr);
        var w = wr.ForkInParens();
        wr.Write($".(*{UserDefinedTypeName(to.AsNewtype, true)})");
        return w;
      }
      if (from != null && from.AsNewtype != null && to.IsTraitType && (enclosingMethod != null || enclosingFunction != null)) {
        return ToFatPointer(from, wr);
      }

      from = from == null ? null : DatatypeWrapperEraser.SimplifyType(Options, from);
      to = DatatypeWrapperEraser.SimplifyType(Options, to);
      if (from != null && from.IsArrowType && to.IsArrowType && !from.Equals(to)) {
        // Need to convert functions more often, so do this before the
        // EqualsUpToParameters check below
        ArrowType fat = from.AsArrowType, tat = to.AsArrowType;
        // We must wrap the whole conversion in an IIFE to avoid capturing the source expression
        var bvName = idGenerator.FreshId("coer");
        // Nothing interesting should be written to wStmts
        var blackHole = new ConcreteSyntaxTree();
        CreateIIFE(bvName, fat, tok, tat, tok, wr, ref blackHole, out var ans, out wr);

        wr.Write("func (");
        var sep = "";
        var args = new List<string>();
        foreach (Type toArgType in tat.Args) {
          var arg = idGenerator.FreshId("arg");
          args.Add(arg);
          wr.Write("{0}{1} {2}", sep, arg, TypeName(toArgType, wr, tok));
          sep = ", ";
        }
        wr.Write(')');
        if (tat.Result != null) {
          wr.Write(" {0}", TypeName(tat.Result, wr, tok));
        }
        var wBody = wr.NewExprBlock("");
        ConcreteSyntaxTree wCall;
        if (fat.Result == null) {
          wCall = wBody;
        } else {
          wBody.Write("return ");
          wCall = EmitCoercionIfNecessary(@from: fat.Result, to: tat.Result, tok: tok, wr: wBody);
        }
        wCall.Write("{0}(", bvName);
        Contract.Assert(fat.Args.Count == tat.Args.Count);
        sep = "";
        for (int i = 0; i < fat.Args.Count; i++) {
          var fromArgType = fat.Args[i];
          var toArgType = tat.Args[i];
          wCall.Write(sep);
          var w = EmitCoercionIfNecessary(@from: toArgType, to: fromArgType, tok: tok, wr: wCall);
          w.Write(args[i]);
          sep = ", ";
        }
        wCall.Write(')');
        wBody.WriteLine();
        return ans;
      } else if (to.IsTypeParameter || (from != null && EqualsUpToParameters(from, to))) {
        // do nothing
        return wr;
      } else if (from != null && !from.IsTypeParameter && from.IsSubtypeOf(to, true, true)) {
        // upcast
        return wr;
      } else if (from == null || from.IsTypeParameter || to.IsSubtypeOf(from, true, true)) {
        // downcast (allowed?) or implicit cast from parameter
        if (to.IsObjectQ || to.IsObject) {
          // a cast to any can be omitted
          return wr;
        } else if (to.IsTraitType) {
          wr.Write("{0}.CastTo_(", TypeName_Companion(to.AsTraitType, wr, tok));
          var w = wr.Fork();
          wr.Write(")");
          return w;
        } else if (to.IsArrayType) {
          wr.Write("_dafny.ArrayCastTo(");
          var w = wr.Fork();
          wr.Write(")");
          return w;
        } else {
          var w = wr.Fork();
          wr.Write(".({0})", TypeName(to, wr, tok));
          return w;
        }
      } else if (from.AsNewtype is { } fromNewtypeDecl) {
        return EmitCoercionIfNecessary(fromNewtypeDecl.ConcreteBaseType(from.TypeArgs), to, tok, wr, toOrig);
      } else {
        // It's unclear to me whether it's possible to hit this case with a valid Dafny program,
        // so I'm not using UnsupportedFeatureError for now.
        Error(GeneratorErrors.ErrorId.c_Go_infeasible_conversion, tok, wr, "Cannot convert from {0} to {1}", from, to);
        return wr;
      }
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IOrigin tok, ConcreteSyntaxTree wr) {
      if (to.IsTraitType) {
        wr.Write("{0}.CastTo_(", TypeName_Companion(to.AsTraitType, wr, tok));
        var w = wr.Fork();
        wr.Write(")");
        return w;
      }
      return base.EmitDowncast(from, to, tok, wr);
    }

    protected override ConcreteSyntaxTree EmitCoercionToNativeInt(ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      wr.Write(".(int)");
      return w;
    }

    protected override ConcreteSyntaxTree EmitCoercionToArbitraryTuple(ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      wr.Write(".(_dafny.Tuple)");
      return w;
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IOrigin tok, List<Expression> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (ct is SetType) {
        wr.Write("_dafny.SetOf");
      } else if (ct is MultiSetType) {
        wr.Write("_dafny.MultiSetOf");
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        if (ct.Arg.IsCharType && !UnicodeCharEnabled) {
          wr.Write("_dafny.SeqOfChars");
        } else {
          wr.Write("_dafny.SeqOf");
        }
      }
      TrExprList(elements, wr, inLetExprBody, wStmts, typeAt: _ => ct.Arg);
    }

    protected override void EmitMapDisplay(MapType mt, IOrigin tok, List<MapDisplayEntry> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("_dafny.NewMapBuilder().ToMap()");
      foreach (MapDisplayEntry p in elements) {
        wr.Write(".UpdateUnsafe(");
        wr.Append(Expr(p.A, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(Expr(p.B, inLetExprBody, wStmts));
        wr.Write(')');
      }
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write("_dafny.NewBuilder()");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write("_dafny.NewMapBuilder()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      var wStmts = wr.Fork();
      wr.Write("{0}.Add(", collName);
      wr.Append(Expr(elmt, inLetExprBody, wStmts));
      wr.WriteLine(")");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IOrigin tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("{0}.Add(", collName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      wr.Append(Expr(term, inLetExprBody, wStmts));
      wr.WriteLine(")");
      return termLeftWriter;
    }

    protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      if (ct is SetType) {
        wr.Write(collName + ".ToSet()");
      } else {
        Contract.Assert(ct is MapType);
        wr.Write(collName + ".ToMap()");
      }
    }

    protected override (Type, Action<ConcreteSyntaxTree>) EmitIntegerRange(Type type, Action<ConcreteSyntaxTree> wLo, Action<ConcreteSyntaxTree> wHi) {
      Type result;
      if (AsNativeType(type) != null) {
        result = type;
      } else {
        result = new IntType();
      }

      return (result, (wr) => {
        if (AsNativeType(type) != null) {
          wr.Write("{0}.IntegerRange(", TypeName_Companion(type.AsNewtype, wr, tok: Token.NoToken));
        } else {
          wr.Write($"{HelperModulePrefix}IntegerRange(");
        }

        wLo(wr);
        wr.Write(", ");
        wHi(wr);
        wr.Write(')');
      }
      );
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody, wStmts);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var funcBlock = wr.NewBlock("func()", close: BlockStyle.Brace);
      var deferBlock = funcBlock.NewBlock("defer func()", close: BlockStyle.Brace);
      var ifRecoverBlock = deferBlock.NewBlock("if r := recover(); r != nil");
      var stringMaker = UnicodeCharEnabled ? "UnicodeSeqOfUtf8Bytes" : "SeqOfString";
      ifRecoverBlock.WriteLine($"var {haltMessageVarName} = {HelperModulePrefix}{stringMaker}(r.(string))");
      TrStmt(recoveryBody, ifRecoverBlock);
      funcBlock.WriteLine("()");
      TrStmt(body, funcBlock);
      wr.WriteLine("()");
    }
  }
}
