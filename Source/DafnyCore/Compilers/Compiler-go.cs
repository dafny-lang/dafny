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
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using static Microsoft.Dafny.ConcreteSyntaxTreeUtils;

namespace Microsoft.Dafny.Compilers {
  public class GoCompiler : ConcreteSinglePassCompiler {
    public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
      base.OnPreCompile(reporter, otherFileNames);
      if (DafnyOptions.O.CoverageLegendFile != null) {
        Imports.Add(new Import { Name = "DafnyProfiling", Path = "DafnyProfiling" });
      }
    }

    public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".go" };

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.MethodSynthesis,
      Feature.ExternalConstructors,
      Feature.SubsetTypeTests,
      Feature.AllUnderscoreExternalModuleNames
    };


    public override string TargetLanguage => "Go";
    public override string TargetExtension => "go";
    public override string TargetBaseDir(string dafnyProgramName) =>
      $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-go/src";

    public override bool SupportsInMemoryCompilation => false;
    public override bool TextualTargetIsExecutable => false;

    static string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter || tp is OpaqueTypeDecl);
      return $"_default_{tp.CompileName}";
    }

    private readonly List<Import> Imports = new List<Import>(StandardImports);
    private string ModuleName;
    private ConcreteSyntaxTree RootImportWriter;
    private ConcreteSyntaxTree RootImportDummyWriter;

    private string MainModuleName;
    private static List<Import> StandardImports =
      new List<Import> {
        new Import { Name = "_dafny", Path = "dafny" },
        new Import { Name = "os", Path = "os" },
      };
    private static string DummyTypeName = "Dummy__";

    private struct Import {
      public string Name, Path;
      public bool SuppressDummy;
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("// Dafny program {0} compiled into Go", program.Name);

      ModuleName = MainModuleName = program.MainMethod != null ? "main" : Path.GetFileNameWithoutExtension(program.Name);

      wr.WriteLine("package {0}", ModuleName);
      wr.WriteLine();
      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter, out RootImportDummyWriter);

      var rt = wr.NewFile("dafny/dafny.go");
      ReadRuntimeSystem(program, "DafnyRuntime.go", rt);
    }

    protected override void EmitBuiltInDecls(BuiltIns builtIns, ConcreteSyntaxTree wr) {
    }

    const string DafnyTypeDescriptor = "_dafny.TypeDescriptor";

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

      foreach (var import in Imports) {
        EmitImport(import, importWriter, importDummyWriter);
      }
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), wr, mainMethod.tok, mainMethod);

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
      var wr = ((GoCompiler.ClassWriter)cw).ConcreteMethodWriter;
      return wr.NewNamedBlock("func (_this * {0}) Main({1} _dafny.Seq)", FormatCompanionTypeName(((GoCompiler.ClassWriter)cw).ClassName), argsParameterName);
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, ConcreteSyntaxTree wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }

      string pkgName;
      if (libraryName != null) {
        pkgName = libraryName;
      } else {
        // Go ignores all filenames starting with underscores.  So we're forced
        // to rewrite "__default" to "default__".
        pkgName = moduleName;
        if (pkgName != "" && pkgName.All(c => c == '_')) {
          UnsupportedFeatureError(Token.NoToken, Feature.AllUnderscoreExternalModuleNames,
            "Cannot have a package name with only underscores: {0}", wr, pkgName);
          return wr;
        }
        while (pkgName.StartsWith("_")) {
          pkgName = pkgName.Substring(1) + "_";
        }
      }

      var import = new Import { Name = moduleName, Path = pkgName };
      if (isExtern) {
        // Allow the library name to be "" to import built-in things like the error type
        if (pkgName != "") {
          import.SuppressDummy = true;
          AddImport(import);
        }
        return new ConcreteSyntaxTree(); // ignore contents of extern module
      } else {
        var filename = string.Format("{0}/{0}.go", pkgName);
        var w = wr.NewFile(filename);
        ModuleName = moduleName;
        EmitModuleHeader(w);

        AddImport(import);

        return w;
      }
    }

    protected override void FinishModule() {
      ModuleName = MainModuleName;
    }

    private void AddImport(Import import) {
      // Import in root module
      EmitImport(import, RootImportWriter, RootImportDummyWriter);
      // Import in all subsequent modules
      Imports.Add(import);
    }

    private void EmitImport(Import import, ConcreteSyntaxTree importWriter, ConcreteSyntaxTree importDummyWriter) {
      var id = IdProtect(import.Name);
      var path = import.Path;

      importWriter.WriteLine("{0} \"{1}\"", id, path);

      if (!import.SuppressDummy) {
        if (id == "os") {
          importDummyWriter.WriteLine("var _ = os.Args");
        } else {
          importDummyWriter.WriteLine("var _ {0}.{1}", id, DummyTypeName);
        }
      }
    }

    protected override string GetHelperModuleName() => "_dafny";

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string/*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var isDefaultClass = cls is ClassDecl c && c.IsDefaultClass;
      return CreateClass(name, isExtern, fullPrintName, typeParameters, superClasses, tok, wr, includeRtd: !isDefaultClass, includeEquals: true);
    }

    // TODO Consider splitting this into two functions; most things seem to bepassing includeRtd: false and includeEquals: false.
    private GoCompiler.ClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr, bool includeRtd, bool includeEquals) {
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
      // func (_this type_Class_) Default() interface{} {
      //   return (*Class)(nil)
      // }
      //
      // func (_this type_Class_) String() string {
      //   return "module.Class"
      // }
      //
      name = Capitalize(name);

      var w = CreateDescribedSection("class {0}", wr, name);

      var instanceFieldWriter = w.NewBlock(string.Format("type {0} struct", name));

      w.WriteLine();
      CreateInitializer(name, w, out var instanceFieldInitWriter, out var traitInitWriter, out var rtdParamWriter);

      if (typeParameters != null) {
        WriteRuntimeTypeDescriptorsFields(typeParameters, false, instanceFieldWriter, instanceFieldInitWriter, rtdParamWriter);
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
      var wString = w.NewNamedBlock("func (*{0}) String() string", name);
      // Be consistent with other back ends, which don't fold _module into the main module
      var module = ModuleName == MainModuleName ? "_module" : ModuleName;
      wString.WriteLine("return \"{0}.{1}\"", module, name);

      if (includeRtd) {
        ConcreteSyntaxTree wDefault;
        CreateRTD(name, typeParameters, out wDefault, w);

        wDefault.WriteLine("return (*{0})(nil)", name);
      }

      var cw = new ClassWriter(this, name, isExtern, null, w, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);

      if (superClasses != null) {
        superClasses = superClasses.Where(trait => !trait.IsObject).ToList();

        // Emit a method that returns the ID of each parent trait
        var parentTraitsWriter = w.NewBlock($"func (_this *{name}) ParentTraits_() []*_dafny.TraitID");
        parentTraitsWriter.WriteLine("return [](*_dafny.TraitID){{{0}}};", Util.Comma(superClasses, parent => {
          var trait = ((UserDefinedType)parent).ResolvedClass;
          return TypeName_Companion(trait, parentTraitsWriter, tok) + ".TraitID_";
        }));

        foreach (Type typ in superClasses) {
          // Emit a compile-time sanity check that the class emitted does indeed have the methods required by the parent trait
          w.WriteLine("var _ {0} = &{1}{{}}", TypeName(typ, w, tok), name);
        }

        w.WriteLine("var _ _dafny.TraitOffspring = &{0}{{}}", name);
      }
      return cw;
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr) {
      //
      // type Trait interface {
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
      // func (_static *companionStruct_Trait) CastTo_(x interface{}) Trait {
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

      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));
      var wCastTo = wr.NewNamedBlock("func ({0}) CastTo_(x interface{{}}) {1}", FormatCompanionTypeName(name), name);
      wCastTo.WriteLine("var t {0}", name);
      wCastTo.WriteLine("t, _ = x.({0})", name);
      wCastTo.WriteLine("return t");

      var cw = new ClassWriter(this, name, isExtern, abstractMethodWriter, concreteMethodWriter, null, null, null, staticFieldWriter, staticFieldInitWriter);
      staticFieldWriter.WriteLine("TraitID_ *_dafny.TraitID");
      staticFieldInitWriter.WriteLine("TraitID_: &_dafny.TraitID{},");
      return cw;
    }

    protected void CreateInitializer(string name, ConcreteSyntaxTree wr, out ConcreteSyntaxTree instanceFieldInitWriter, out ConcreteSyntaxTree traitInitWriter, out ConcreteSyntaxTree rtdParamWriter) {
      wr.Write("func {0}(", FormatInitializerName(name));
      rtdParamWriter = wr.Fork();
      var w = wr.NewNamedBlock(") *{0}", name);
      w.WriteLine("_this := {0}{{}}", name);

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
      var cw = CreateClass(IdName(iter), false, null, iter.TypeArgs, null, null, wr, includeRtd: false, includeEquals: false);

      cw.InstanceFieldWriter.WriteLine("cont chan<- struct{}");
      cw.InstanceFieldWriter.WriteLine("yielded <-chan struct{}");

      Constructor ct = null;
      foreach (var member in iter.Members) {
        if (member is Field f && !f.IsGhost) {
          cw.DeclareField(IdName(f), iter, false, false, f.Type, f.tok, PlaceboValue(f.Type, wr, f.tok, true), f);
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
          cw.ConcreteMethodWriter.Write("{0}{1} {2}", sep, IdName(p), TypeName(p.Type, wr, p.tok));
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
      // func (_this Dt) Get() Data_Dt_ {
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
      // func (_this Dt) EqualsGeneric(other interface{}) bool { ... }
      //
      // func (CompanionStruct_Dt_) AllSingletonConstructors() _dafny.Iterator {
      //   i := -1
      //   return func() (interface{}, bool) {
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
      // func (ty type_Dt_) Default() interface{} {
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
      //   Get() Data_Dt_
      // }
      //
      // type lazyDt struct {
      //   value Iface_Dt_
      //   init func() Dt
      // }
      //
      // func (_this * lazyDt) Get() *Iface_Dt {
      //   if _this.value == nil {
      //      _this.value = _this.init().Get()
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
      // func (_this * Dt_Ctor0) Get() Dt {
      //   return _this
      // }
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.go
        return null;
      }

      string name = Capitalize(dt.CompileName);
      string companionTypeName = FormatCompanionTypeName(name);
      string dataName = FormatDatatypeInterfaceName(name);
      string ifaceName = FormatLazyInterfaceName(name);
      var simplifiedType = DatatypeWrapperEraser.SimplifyType(UserDefinedType.FromTopLevelDecl(dt.tok, dt));
      var simplifiedTypeName = TypeName(simplifiedType, wr, dt.tok);

      Func<DatatypeCtor, string> structOfCtor = ctor =>
        string.Format("{0}{1}_{2}", dt is CoDatatypeDecl ? "*" : "", name, ctor.CompileName);

      // from here on, write everything into the new block created here:
      wr = CreateDescribedSection("{0} {1}", wr, dt.WhatKind, name);

      if (dt is IndDatatypeDecl) {
        var wStruct = wr.NewNamedBlock("type {0} struct", name);
        wStruct.WriteLine(dataName);

        wr.WriteLine();
        var wGet = wr.NewNamedBlock("func (_this {0}) Get() {1}", name, dataName);
        wGet.WriteLine("return _this.{0}", dataName);
      } else {
        var wDt = wr.NewNamedBlock("type {0} struct", name);
        wDt.WriteLine(ifaceName);

        wr.WriteLine();
        var wIface = wr.NewNamedBlock("type {0} interface", ifaceName);
        wIface.WriteLine("Get() {0}", dataName);

        wr.WriteLine();
        var wLazy = wr.NewNamedBlock("type lazy_{0}_ struct", name);
        wLazy.WriteLine("value {0}", dataName);
        wLazy.WriteLine("init func() {0}", name);

        wr.WriteLine();
        var wLazyGet = wr.NewNamedBlock("func (_this *lazy_{0}_) Get() {1}", name, dataName);
        var wIf = wLazyGet.NewBlock("if _this.value == nil");
        wIf.WriteLine("_this.value = _this.init().Get()");
        wIf.WriteLine("_this.init = nil"); // allow GC of values in closure

        wLazyGet.WriteLine("return _this.value");

        wr.WriteLine();
        var wLazyCreate = wr.NewNamedBlock("func ({0}) {1}(f func () {2}) {2}", companionTypeName, FormatLazyConstructorName(name), name, name);
        wLazyCreate.WriteLine("return {0}{{&lazy_{0}_{{nil, f}}}}", name);
      }

      {
        wr.WriteLine();
        var wIface = wr.NewNamedBlock("type {0} interface", dataName);
        wIface.WriteLine("is{0}()", name);
      }

      wr.WriteLine();
      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", companionTypeName);
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), companionTypeName);

      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        var ctorStructName = name + "_" + ctor.CompileName;
        wr.WriteLine();
        var wStruct = wr.NewNamedBlock("type {0} struct", ctorStructName);
        var k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            wStruct.WriteLine("{0} {1}", DatatypeFieldName(formal, k), TypeName(formal.Type, wr, formal.Tok));
            k++;
          }
        }

        wr.WriteLine();
        wr.WriteLine("func ({0}{1}) is{2}() {{}}", dt is CoDatatypeDecl ? "*" : "", ctorStructName, name);
        wr.WriteLine();

        wr.Write("func ({0}) {1}(", companionTypeName, FormatDatatypeConstructorName(ctor.CompileName));
        var argNames = new List<string>();
        k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            var formalName = DatatypeFieldName(formal, k);

            wr.Write("{0}{1} {2}", k > 0 ? ", " : "", formalName, TypeName(formal.Type, wr, formal.Tok));

            argNames.Add(formalName);
            k++;
          }
        }
        var wCreateBody = wr.NewNamedBlock(") {0}", name);
        wCreateBody.WriteLine("return {0}{{{1}{2}{{{3}}}}}", name, dt is CoDatatypeDecl ? "&" : "", ctorStructName, Util.Comma(argNames));

        wr.WriteLine();
        var wCheck = wr.NewNamedBlock("func (_this {0}) {1}() bool", name, FormatDatatypeConstructorCheckName(ctor.CompileName));
        wCheck.WriteLine("_, ok := _this.Get().({0})", structOfCtor(ctor));
        wCheck.WriteLine("return ok");

        if (dt is CoDatatypeDecl) {
          wr.WriteLine();
          var wGet = wr.NewNamedBlock("func (_this *{0}) Get() {1}", ctorStructName, dataName);
          wGet.WriteLine("return _this");
        }
      }

      /* func (_static CompanionStruct_Dt_) Default(_default_A interface{}, _default_B interface{}) Dt {
       *   return Dt{Dt_GroundingCtor{...}}
       * }
       */
      wr.WriteLine();
      wr.Write($"func ({companionTypeName}) Default(");
      wr.Write(Util.Comma(UsedTypeParameters(dt), tp => $"{FormatDefaultTypeParameterValue(tp)} interface{{}}"));
      {
        var wDefault = wr.NewBlock($") {simplifiedTypeName}");
        wDefault.Write("return ");
        var groundingCtor = dt.GetGroundingCtor();
        if (groundingCtor.IsGhost) {
          wDefault.Write(ForcePlaceboValue(simplifiedType, wDefault, dt.tok));
        } else if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(dt, out var innerType)) {
          wDefault.Write(DefaultValue(innerType, wDefault, dt.tok));
        } else {
          var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
          var arguments = Util.Comma(nonGhostFormals, f => DefaultValue(f.Type, wDefault, f.tok));
          EmitDatatypeValue(dt, groundingCtor, dt is CoDatatypeDecl, arguments, wDefault);
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
          wSingles.WriteLine("case {0}: return {1}.{2}(), true", i, FormatCompanionName(name), FormatDatatypeConstructorName(ctor.CompileName));
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
              var wDtor = wr.NewNamedBlock("func (_this {0}) {1}() {2}", name, FormatDatatypeDestructorName(arg.CompileName), TypeName(arg.Type, wr, arg.tok));
              var n = dtor.EnclosingCtors.Count;
              if (n == 1) {
                wDtor.WriteLine("return _this.Get().({0}).{1}", structOfCtor(dtor.EnclosingCtors[0]), DatatypeFieldName(arg));
              } else {
                wDtor = wDtor.NewBlock("switch data := _this.Get().(type)");
                var compiledConstructorsProcessed = 0;
                for (var i = 0; i < n; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  if (ctor_i.IsGhost) {
                    continue;
                  }
                  if (compiledConstructorsProcessed < compiledConstructorCount - 1) {
                    wDtor.WriteLine("case {0}: return data.{1}", structOfCtor(ctor_i), DatatypeFieldName(arg));
                  } else {
                    wDtor.WriteLine("default: return data.({0}).{1}", structOfCtor(ctor_i), DatatypeFieldName(arg));
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
        w = w.NewNamedBlock("switch {0}_this.Get().(type)", needData ? "data := " : "");
        w.WriteLine("case nil: return \"null\"");
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          var wCase = w.NewNamedBlock("case {0}:", structOfCtor(ctor));
          var nm = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") + dt.Name + "." + ctor.Name;
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
                  wCase.Write("{0}data.{1}.VerbatimString(true)", sep, DatatypeFieldName(arg, k));
                } else {
                  wCase.Write("{0}_dafny.String(data.{1})", sep, DatatypeFieldName(arg, k));
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
          wDefault.WriteLine("return \"{0}.{1}.unexpected\"", dt.EnclosingModuleDefinition.CompileName, dt.CompileName);
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

        wEquals = wEquals.NewNamedBlock("switch {0}_this.Get().(type)", needData1 ? "data1 := " : "");
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          var wCase = wEquals.NewNamedBlock("case {0}:", structOfCtor(ctor));

          var needData2 = ctor.Formals.Exists(arg => !arg.IsGhost);

          wCase.WriteLine("{0}, ok := other.Get().({1})", needData2 ? "data2" : "_", structOfCtor(ctor));
          wCase.Write("return ok");
          var k = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              wCase.Write(" && ");
              string nm = DatatypeFieldName(arg, k);
              var eqType = DatatypeWrapperEraser.SimplifyType(arg.Type);
              if (IsDirectlyComparable(eqType)) {
                wCase.Write("data1.{0} == data2.{0}", nm);
              } else if (IsOrderedByCmp(eqType)) {
                wCase.Write("data1.{0}.Cmp(data2.{0}) == 0", nm);
              } else if (IsComparedByEquals(eqType)) {
                wCase.Write("data1.{0}.Equals(data2.{0})", nm);
              } else {
                wCase.Write("_dafny.AreEqual(data1.{0}, data2.{0})", nm);
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
        var usedTypeParams = UsedTypeParameters(dt);
        CreateRTD(name, usedTypeParams, out var wDefault, wr);

        WriteRuntimeTypeDescriptorsLocals(usedTypeParams, true, wDefault);

        var arguments = Util.Comma(UsedTypeParameters(dt), tp => DefaultValue(new UserDefinedType(tp), wDefault, dt.tok, true));
        wDefault.WriteLine($"return {TypeName_Companion(dt, wr, dt.tok)}.Default({arguments});");
      }

      return new ClassWriter(this, name, dt.IsExtern(out _, out _), null, wr, wr, wr, wr, staticFieldWriter, staticFieldInitWriter);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = CreateClass(IdName(nt), false, null, null, null, null, wr, includeRtd: false, includeEquals: false);
      var w = cw.ConcreteMethodWriter;
      var nativeType = nt.NativeType != null ? GetNativeTypeName(nt.NativeType) : null;
      if (nt.NativeType != null) {
        var wIntegerRangeBody = w.NewNamedBlock("func (_this *{0}) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator", FormatCompanionTypeName(IdName(nt)));
        wIntegerRangeBody.WriteLine("iter := _dafny.IntegerRange(lo, hi)");
        var wIterFuncBody = wIntegerRangeBody.NewBlock("return func() (interface{}, bool)");
        wIterFuncBody.WriteLine("next, ok := iter()");
        wIterFuncBody.WriteLine("if !ok {{ return {0}(0), false }}", nativeType);
        wIterFuncBody.WriteLine("return next.(_dafny.Int).{0}(), true", Capitalize(nativeType));
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var retType = nativeType ?? TypeName(nt.BaseType, w, nt.tok);
        var wWitness = w.NewNamedBlock("func (_this *{0}) Witness() {1}", FormatCompanionTypeName(IdName(nt)), retType);
        var wStmts = wWitness.Fork();
        wWitness.Write("return ");
        if (nt.NativeType == null) {
          wWitness.Append(TrExpr(nt.Witness, false, wStmts));
          wWitness.WriteLine();
        } else {
          TrParenExpr(nt.Witness, wWitness, false, wStmts);
          wWitness.WriteLine(".{0}()", Capitalize(GetNativeTypeName(nt.NativeType)));
        }
      }
      // RTD
      {
        CreateRTD(IdName(nt), null, out var wDefaultBody, wr);
        var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
        var d = TypeInitializationValue(udt, wr, nt.tok, false, true);
        wDefaultBody.WriteLine("return {0}", d);
      }
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = CreateClass(IdName(sst), false, null, sst.TypeArgs, null, null, wr, includeRtd: false, includeEquals: false);
      var w = cw.ConcreteMethodWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        var wStmts = w.Fork();
        witness.Append(TrExpr(sst.Witness, false, wStmts));
        DeclareField("Witness", false, true, true, sst.Rhs, sst.tok, witness.ToString(), cw.ClassName, cw.StaticFieldWriter, cw.StaticFieldInitWriter, cw.ConcreteMethodWriter);
      }
      // RTD
      {
        CreateRTD(IdName(sst), null, out var wDefaultBody, wr);
        var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
        var d = TypeInitializationValue(udt, wr, sst.tok, false, true);
        wDefaultBody.WriteLine("return {0}", d);
      }
    }

    private void CreateRTD(string typeName, List<TypeParameter>/*?*/ usedParams, out ConcreteSyntaxTree wDefaultBody, ConcreteSyntaxTree wr) {
      Contract.Requires(typeName != null);
      Contract.Requires(wr != null);
      Contract.Ensures(Contract.ValueAtReturn(out wDefaultBody) != null);

      if (usedParams == null) {
        usedParams = new List<TypeParameter>();
      }
      wr.WriteLine();
      wr.Write("func {0}(", FormatRTDName(typeName));
      WriteRuntimeTypeDescriptorsFormals(usedParams, true, wr);
      var wTypeMethod = wr.NewBlock($") {DafnyTypeDescriptor}");
      wTypeMethod.WriteLine("return type_{0}_{{{1}}}", typeName, Util.Comma(usedParams, tp => FormatRTDName(tp.CompileName)));

      wr.WriteLine();
      var wType = wr.NewNamedBlock("type type_{0}_ struct", typeName);
      WriteRuntimeTypeDescriptorsFields(usedParams, true, wType, null, null);

      wr.WriteLine();
      wDefaultBody = wr.NewNamedBlock("func (_this type_{0}_) Default() interface{{}}", typeName);

      wr.WriteLine();
      var wString = wr.NewNamedBlock("func (_this type_{0}_) String() string", typeName);
      wString.WriteLine("return \"{0}.{1}\"", ModuleName, typeName);
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
          throw new cce.UnreachableException();  // to please the compiler
      }
    }
    protected class ClassWriter : IClassWriter {
      public readonly GoCompiler Compiler;
      public readonly string ClassName;
      public readonly bool IsExtern;
      public readonly ConcreteSyntaxTree/*?*/ AbstractMethodWriter, ConcreteMethodWriter, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter;
      public bool AnyInstanceFields { get; private set; } = false;

      public ClassWriter(GoCompiler compiler, string className, bool isExtern, ConcreteSyntaxTree abstractMethodWriter, ConcreteSyntaxTree concreteMethodWriter,
        ConcreteSyntaxTree/*?*/ instanceFieldWriter, ConcreteSyntaxTree/*?*/ instanceFieldInitWriter, ConcreteSyntaxTree/*?*/ traitInitWriter,
        ConcreteSyntaxTree staticFieldWriter, ConcreteSyntaxTree staticFieldInitWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(className != null);
        this.Compiler = compiler;
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

      public ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.tok, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance, lookasideBody);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, member, ClassName, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, createBody, member, ClassName, out setterWriter, AbstractMethodWriter, ConcreteMethodWriter, forBodyInheritance);
      }
      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field field) {
        // FIXME: This should probably be done in Compiler.DeclareField().
        // Should just have these delegate methods take the ClassWriter as an
        // argument.
        if (!isStatic) {
          AnyInstanceFields = true;
        }
        Compiler.DeclareField(name, IsExtern, isStatic, isConst, type, tok, rhs, ClassName, FieldWriter(isStatic), FieldInitWriter(isStatic), ConcreteMethodWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        var tok = field.tok;
        var lvalue = Compiler.EmitMemberSelect(w => w.Write("_this"), UserDefinedType.FromTopLevelDecl(tok, enclosingClass), field,
        new List<TypeArgumentInstantiation>(), enclosingClass.ParentFormalTypeParametersToActuals, instantiatedFieldType);
        var wRHS = lvalue.EmitWrite(FieldInitWriter(false));
        Compiler.EmitCoercionIfNecessary(instantiatedFieldType, field.Type, tok, wRHS);
        wRHS.Write(Compiler.PlaceboValue(instantiatedFieldType, ErrorWriter(), tok));
      }

      public ConcreteSyntaxTree/*?*/ ErrorWriter() => ConcreteMethodWriter;

      public void Finish() {
        Compiler.FinishClass(this);
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, string ownerName, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance, bool lookasideBody) {
      var overriddenIns = m.EnclosingClass is TraitDecl && !forBodyInheritance ? null : m.OverriddenMethod?.Original.Ins;
      var overriddenOuts = m.EnclosingClass is TraitDecl && !forBodyInheritance ? null : m.OverriddenMethod?.Original.Outs;
      return CreateSubroutine(IdName(m), typeArgs, m.Ins, m.Outs, null,
        overriddenIns, overriddenOuts, null,
        m.tok, m.IsStatic, createBody, ownerName, m, abstractWriter, concreteWriter, forBodyInheritance, lookasideBody);
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody,
      MemberDecl member, string ownerName, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance, bool lookasideBody) {

      var fnOverridden = (member as Function)?.OverriddenFunction?.Original;
      return CreateSubroutine(name, typeArgs, formals, new List<Formal>(), resultType,
        fnOverridden?.Formals, fnOverridden == null ? null : new List<Formal>(), fnOverridden?.ResultType,
        tok, isStatic, createBody, ownerName, member, abstractWriter, concreteWriter, forBodyInheritance, lookasideBody);
    }

    private ConcreteSyntaxTree CreateSubroutine(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> inParams, List<Formal> outParams, Type/*?*/ resultType,
      List<Formal>/*?*/ overriddenInParams, List<Formal>/*?*/ overriddenOutParams, Type/*?*/ overriddenResultType,
      IToken tok, bool isStatic, bool createBody, string ownerName, MemberDecl/*?*/ member, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter,
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
        if (member != null && member.EnclosingClass is DatatypeDecl) {
          wr.Write("func ({0} {1}) ", isStatic || customReceiver ? "_static" : "_this", receiver);
        } else {
          wr.Write("func ({0} *{1}) ", isStatic || customReceiver ? "_static" : "_this", receiver);
        }
      } else {
        wr = abstractWriter;
      }
      wr.Write("{0}(", name);
      var prefix = "";
      var nTypes = WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, lookasideBody), wr, ref prefix, tp => $"{FormatRTDName(tp.CompileName)} {DafnyTypeDescriptor}");
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
            if (!instantiatedType.Equals(p.Type)) {
              // var p instantiatedType = p.(instantiatedType)
              var pName = IdName(inParams[i]);
              DeclareLocalVar(pName, instantiatedType, p.tok, true, null, w);
              var wRhs = EmitAssignmentRhs(w);
              wRhs = EmitCoercionIfNecessary(p.Type, instantiatedType, p.tok, wRhs);
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

    protected void WriteOutTypes(List<Formal> outParams, Type/*?*/ resultType, ConcreteSyntaxTree wr, IToken tok) {
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

    void WriteRuntimeTypeDescriptorsFields(List<TypeParameter> typeParams, bool useAllTypeArgs, ConcreteSyntaxTree/*?*/ wr, ConcreteSyntaxTree/*?*/ wInit, ConcreteSyntaxTree/*?*/ wParams) {
      Contract.Requires(typeParams != null);

      var sep = "";
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          var name = FormatRTDName(tp.CompileName);

          if (wr != null) {
            wr.WriteLine($"{name} {DafnyTypeDescriptor}");
          }

          if (wInit != null) {
            wInit.WriteLine("_this.{0} = {0}", name);
          }

          if (wParams != null) {
            wParams.Write($"{sep}{name} {DafnyTypeDescriptor}");
            sep = ", ";
          }
        }
      }
    }

    void WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, ConcreteSyntaxTree wr) {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      var prefix = "";
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          wr.Write($"{prefix}{FormatRTDName(tp.CompileName)} {DafnyTypeDescriptor}");
          prefix = ", ";
        }
      }
    }

    void WriteRuntimeTypeDescriptorsLocals(List<TypeParameter> typeParams, bool useAllTypeArgs, ConcreteSyntaxTree wr) {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          wr.WriteLine("{0} := _this.{0}", FormatRTDName(tp.CompileName));
          EmitDummyVariableUse(FormatRTDName(tp.CompileName), wr);
        }
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

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      var xType = DatatypeWrapperEraser.SimplifyType(type, true);
      if (xType is BoolType) {
        return "_dafny.BoolType";
      } else if (xType is CharType) {
        return "_dafny.CharType";
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
        return string.Format("{0}{1}", thisContext != null && tp.Parent is ClassDecl && !(tp.Parent is TraitDecl) ? "_this." : "", FormatRTDName(tp.CompileName));
      } else if (xType.IsBuiltinArrowType) {
        return string.Format("_dafny.CreateStandardTypeDescriptor({0})", TypeInitializationValue(xType, wr, tok, false, true));
      } else if (xType is UserDefinedType udt) {
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "_dafny.Int64Type";
        } else if (cl is ClassDecl || cl is DatatypeDecl) {
          var w = new ConcreteSyntaxTree();
          w.Write("{0}(", cl is TupleTypeDecl ? "_dafny.TupleType" : TypeName_RTD(xType, w, tok));
          var typeArgs = cl is DatatypeDecl dt ? UsedTypeParameters(dt, udt.TypeArgs) : TypeArgumentInstantiation.ListFromClass(cl, udt.TypeArgs);
          EmitTypeDescriptorsActuals(typeArgs, udt.tok, w, true);
          w.Write(")");
          return w.ToString();
        } else if (xType.IsNonNullRefType) {
          // what we emit here will only be used to construct a dummy value that programmer-supplied code will overwrite later
          return "_dafny.PossiblyNullType/*not used*/";
        } else {
          Contract.Assert(cl is NewtypeDecl || cl is SubsetTypeDecl);
          return TypeName_RTD(xType, wr, udt.tok) + "()";
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, string ownerName, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance) {
      return CreateFunction(name, new List<TypeArgumentInstantiation>(), new List<Formal>(), resultType, tok, isStatic, createBody, member, ownerName, abstractWriter, concreteWriter, forBodyInheritance, false);
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, string ownerName,
      out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree abstractWriter, ConcreteSyntaxTree concreteWriter, bool forBodyInheritance) {

      var getterWriter = CreateGetter(name, resultType, tok, false, createBody, member, ownerName, abstractWriter, concreteWriter, forBodyInheritance);

      var valueParam = new Formal(tok, "value", resultType, true, false, null);
      setterWriter = CreateSubroutine(name + "_set_", new List<TypeArgumentInstantiation>(), new List<Formal>() { valueParam }, new List<Formal>(), null,
        new List<Formal>() { valueParam }, new List<Formal>(), null, tok, false, createBody, ownerName, member,
        abstractWriter, concreteWriter, forBodyInheritance, false);
      return getterWriter;
    }

    protected override bool SupportsStaticsInGenericClasses => false;
    protected override bool TraitRepeatsInheritedDeclarations => true;

    private void FinishClass(GoCompiler.ClassWriter cw) {
      // Go gets weird about zero-length structs.  In particular, it likes to
      // make all pointers to a zero-length struct the same.  Irritatingly, this
      // forces us to waste space here.
      if (!cw.AnyInstanceFields) {
        cw.InstanceFieldWriter.WriteLine("dummy byte");
      }
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START");
      wr.WriteLine("TAIL_CALL_START:");
      return wr;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START");
    }

    private static string CharTypeName => UnicodeCharEnabled ? "_dafny.CodePoint" : "_dafny.Char";

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(type);
      if (xType is SpecialNativeType snt) {
        return snt.Name;
      } else if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return CharTypeName;
      } else if (xType is IntType) {
        return "_dafny.Int";
      } else if (xType is BigOrdinalType) {
        return "_dafny.Ord";
      } else if (xType is RealType) {
        return "_dafny.Real";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "_dafny.BV";
      } else if (xType.AsNewtype != null && member == null) {  // when member is given, use UserDefinedType case below
        NativeType nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(xType.AsNewtype.BaseType, wr, tok);
      } else if (xType.IsObjectQ) {
        return "interface{}";
      } else if (xType.IsArrayType) {
        return "*_dafny.Array";
      } else if (xType is UserDefinedType udt) {
        var s = FullTypeName(udt, member);
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "ulong";
        } else if (xType is ArrowType at) {
          return string.Format("func ({0}) {1}", Util.Comma(at.Args, arg => TypeName(arg, wr, tok)), TypeName(at.Result, wr, tok));
        } else if (udt.IsTypeParameter) {
          return "interface{}";
        } else if (cl is TupleTypeDecl tupleTypeDecl) {
          return "_dafny.Tuple";
        }
        if (udt.IsTraitType && udt.ResolvedClass.IsExtern(out _, out _)) {
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
        return "_dafny.Set";
      } else if (xType is SeqType) {
        return "_dafny.Seq";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSet";
      } else if (xType is MapType) {
        return "_dafny.Map";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      // When returning nil, explicitly cast the nil so that type assertions work
      string nil() {
        return string.Format("({0})(nil)", TypeName(type, wr, tok));
      }

      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return $"{CharTypeName}({CharType.DefaultValueAsString})";
      } else if (xType is IntType || xType is BigOrdinalType) {
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
          w.Write(TypeDescriptor(udt, wr, udt.tok));
          w.Write(".Default()");
          return w.ToString();
        } else {
          return FormatDefaultTypeParameterValue(tp);
        }
      } else if (cl is OpaqueTypeDecl opaque) {
        return FormatDefaultTypeParameterValue(opaque);
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_Companion(cl, wr, tok) + ".Witness()";
        } else if (td.NativeType != null) {
          return GetNativeTypeName(td.NativeType) + "(0)";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
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
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return nil();
        }
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        // In an auto-init context (like a field initializer), we may not have
        // access to all the type descriptors, so we can't construct the
        // default value, but then an empty structure is an acceptable default, since
        // Dafny proves the value won't be accessed.
        if (usePlaceboValue) {
          return string.Format("{0}{{}}", TypeName(udt, wr, tok));
        }
        var n = dt is TupleTypeDecl ? "_dafny.TupleOf" : $"{TypeName_Companion(dt, wr, tok)}.Default";
        var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs);
        return $"{n}({Util.Comma(relevantTypeArgs, ta => DefaultValue(ta.Actual, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))})";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
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

    protected string TypeName_Related(Func<string, string> formatter, Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
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
      return string.Format("{0}{1}_{2}", ptr, TypeName(UserDefinedType.FromTopLevelDecl(ctor.tok, ctor.EnclosingDatatype), wr, ctor.tok), ctor.CompileName);
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      // XXX This duplicates some of the logic in UserDefinedTypeName, but if we
      // don't do it here, we end up passing the name of the module to
      // FormatCompanionName, which doesn't help anyone
      if (type is UserDefinedType udt && udt.ResolvedClass != null && IsExternMemberOfExternModule(member, udt.ResolvedClass)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!udt.ResolvedClass.EnclosingModuleDefinition.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(udt.ResolvedClass.EnclosingModuleDefinition.CompileName);
      }
      return TypeName_Related(FormatCompanionName, type, wr, tok, member);
    }

    protected string TypeName_CompanionType(Type type, ConcreteSyntaxTree wr, IToken tok) {
      return TypeName_Related(FormatCompanionTypeName, type, wr, tok);
    }

    protected string TypeName_Initializer(Type type, ConcreteSyntaxTree wr, IToken tok) {
      return TypeName_Related(FormatInitializerName, type, wr, tok);
    }

    protected string TypeName_RTD(Type type, ConcreteSyntaxTree wr, IToken tok) {
      return TypeName_Related(FormatRTDName, type, wr, tok);
    }

    protected string ClassName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      return type is UserDefinedType udt ? FullTypeName(udt, member) : TypeName(type, wr, tok, member);
    }

    protected string UnqualifiedClassName(Type type, ConcreteSyntaxTree wr, IToken tok) {
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

    protected override Type NativeForm(Type type) {
      if (type.IsStringType) {
        return NativeStringType;
      } else {
        return type;
      }
    }

    /// A type which is rendered to Go exactly as specified.  Used to represent the native string type.
    private class SpecialNativeType : UserDefinedType {
      internal SpecialNativeType(string name) : base(Token.NoToken, name, null) { }
    }

    private readonly static SpecialNativeType NativeStringType = new SpecialNativeType("string");

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isExtern, bool isStatic, bool isConst, Type type, IToken tok, string/*?*/ rhs, string className, ConcreteSyntaxTree wr, ConcreteSyntaxTree initWriter, ConcreteSyntaxTree concreteMethodWriter) {
      if (isExtern) {
        Error(tok, "Unsupported field {0} in extern trait", wr, name);
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

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write("{0}{1} {2}", prefix, name, TypeName(type, wr, tok));
        return true;
      } else {
        return false;
      }
    }

    private ConcreteSyntaxTree/*?*/ DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, bool includeRhs, bool leaveRoomForRhs, ConcreteSyntaxTree wr) {
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

    void EmitDummyVariableUse(string variableName, ConcreteSyntaxTree wr) {
      Contract.Requires(variableName != null);
      Contract.Requires(wr != null);

      wr.WriteLine("_ = {0}", variableName);
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
      var w = DeclareLocalVar(name, type, tok, includeRhs: (rhs != null || leaveRoomForRhs), leaveRoomForRhs: leaveRoomForRhs, wr: wr);
      if (rhs != null) {
        w.Write(rhs);
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, ConcreteSyntaxTree wr) {
      return DeclareLocalVar(name, type, tok, includeRhs: true, leaveRoomForRhs: false, wr: wr);
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override bool NeedsCastFromTypeParameter => true;
    protected override bool SupportsMultipleReturns => true;
    protected override string StmtTerminator => "";

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      // emit nothing; this is only for actual parametric polymorphism, not RTDs
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, ConcreteSyntaxTree wr, IToken tok) {
      return "var " + target;
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
      var isString = arg.Type.IsStringType;
      var wStmts = wr.Fork();
      if (isString && UnicodeCharEnabled) {
        wr.Write("_dafny.Print(");
        wr.Append(TrExpr(arg, false, wStmts));
        wr.WriteLine(".VerbatimString(false))");
      } else if (!isString ||
                 (arg.Resolved is MemberSelectExpr mse &&
                  mse.Member.IsExtern(out _, out _))) {
        wr.Write("_dafny.Print(");
        wr.Append(TrExpr(arg, false, wStmts));
        wr.WriteLine(")");
      } else {
        wr.Write("_dafny.Print((");
        wr.Append(TrExpr(arg, false, wStmts));
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

    protected override void EmitReturnExpr(Expression expr, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      var w = EmitReturnExpr(wr);
      var fromType = thisContext == null ? expr.Type : expr.Type.Subst(thisContext.ParentFormalTypeParametersToActuals);
      w = EmitCoercionIfNecessary(fromType, resultType, expr.tok, w);
      w.Append(TrExpr(expr, inLetExprBody, wStmts));
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
            wOutParam = EmitCoercionIfNecessary(f.Type.Subst(typeMap), f.Type, f.tok, wr);
          } else if (overriddenOutParams != null) {
            // ignore typeMap
            wOutParam = EmitCoercionIfNecessary(f.Type, overriddenOutParams[i].Type, f.tok, wr);
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
      var w = wr.Fork();
      var prefix = createContinueLabel ? "C" : "L";
      wr.WriteLine($"goto {prefix}{label};");
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

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("panic(");
      if (tok != null) {
        wr.Write("\"" + Dafny.ErrorReporter.TokenToString(tok) + ": \" + ");
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

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {

      wr.Write($"for {loopIndex.CompileName} := ");
      var startWr = wr.Fork();
      wr.Write($"; ");

      ConcreteSyntaxTree bodyWr;
      if (goingUp) {
        if (endVarName == null) {
          wr.Write("true");
        } else if (IsOrderedByCmp(loopIndex.Type)) {
          wr.Write($"{loopIndex.CompileName}.Cmp({endVarName}) < 0");
        } else {
          wr.Write($"{loopIndex.CompileName} < {endVarName}");
        }
        if (AsNativeType(loopIndex.Type) == null) {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName} = {loopIndex.CompileName}.Plus(_dafny.One)");
        } else {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName}++");
        }
      } else {
        if (endVarName == null) {
          wr.Write("true");
        } else if (IsOrderedByCmp(loopIndex.Type)) {
          wr.Write($"{endVarName}.Cmp({loopIndex.CompileName}) < 0");
        } else {
          wr.Write($"{endVarName} < {loopIndex.CompileName}");
        }
        bodyWr = wr.NewBlock($"; ");
        if (AsNativeType(loopIndex.Type) == null) {
          bodyWr.WriteLine($"{loopIndex.CompileName} = {loopIndex.CompileName}.Minus(_dafny.One)");
        } else {
          bodyWr.WriteLine($"{loopIndex.CompileName}--");
        }
      }
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for {0} := _dafny.Zero; {0}.Cmp({1}) < 0; {0} = {0}.Plus(_dafny.One)", indexVar, bound);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for {0} := _dafny.IntOf({1}); ; {0} = {0}.Times(_dafny.Two)", indexVar, start);
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

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
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
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
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
            $"_dafny.InstanceOfTrait/*1*/({tmpVarName}.(_dafny.TraitOffspring), {TypeName_Companion(trait, wPreconditions, tok)}.TraitID_)");
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
      return typeTest == "true" ? null : typeTest;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {

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

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall /*?*/, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is ClassDecl clsDecl && clsDecl.IsObjectTrait) {
        wr.Write("_dafny.New_Object()");
      } else {
        wr.Write("{0}(", TypeName_Initializer(type, wr, tok));
        EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, wr);
        wr.Write(")");
      }
    }

    protected override void EmitNewArray(Type elmtType, IToken tok, List<Expression> dimensions,
        bool mustInitialize, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = DefaultValue(elmtType, wr, tok, true);

      string sep;
      if (!mustInitialize) {
        wr.Write("_dafny.NewArray(");
        sep = "";
      } else {
        wr.Write("_dafny.NewArrayWithValue({0}", initValue);
        sep = ", ";
      }

      foreach (Expression dim in dimensions) {
        wr.Write(sep);
        wr.Append(TrExpr(dim, false, wStmts));
        sep = ", ";
      }

      wr.Write(")");
    }

    protected override ConcreteSyntaxTree EmitLiteralExpr(LiteralExpr e) {
      var wr = new ConcreteSyntaxTree();
      if (e is StaticReceiverExpr) {
        wr.Write("{0}", TypeName_Companion(((UserDefinedType)e.Type).ResolvedClass, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("({0})(nil)", TypeName(e.Type, wr, e.tok));
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
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }

      return wr;
    }
    void EmitIntegerLiteral(BigInteger i, ConcreteSyntaxTree wr) {
      Contract.Requires(wr != null);
      if (i.IsZero) {
        wr.Write("_dafny.Zero");
      } else if (i.IsOne) {
        wr.Write("_dafny.One");
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write("_dafny.IntOfInt64({0})", i);
      } else {
        wr.Write("_dafny.IntOfString(\"{0}\")", i);
      }
    }

    protected void TrCharLiteral(CharLiteralExpr chr, ConcreteSyntaxTree wr) {
      var v = (string)chr.Value;
      wr.Write($"{CharTypeName}(");
      // See comment in TrStringLiteral for why we can't just translate directly sometimes.
      if (!UnicodeCharEnabled && Util.MightContainNonAsciiCharacters(v, false)) {
        var c = Util.UnescapedCharacters(v, false).Single();
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
          foreach (var c in Util.UnescapedCharacters(s, str.IsVerbatim)) {
            wr.Write(comma);
            wr.Write($"{c}");
            comma = ", ";
          }

          wr.Write(")");
        } else {
          wr.Write($"_dafny.SeqOfString(");
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

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string literalSuffix = null;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out _, out literalSuffix, out _);
      }

      if (bvType.NativeType == null) {
        wr.Write('(');
        var middle = wr.Fork();
        wr.Write(").Modulo(_dafny.One.Lsh(_dafny.IntOf({0})))", bvType.Width);
        return middle;
      } else if (bvType.NativeType.Bitwidth == bvType.Width) {
        // no truncation needed
        return wr;
      } else {
        wr.Write("((");
        var middle = wr.Fork();
        // print in hex, because that looks nice
        wr.Write(") & 0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix);
        return middle;
      }
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out _, out _, out needsCast);
      }

      var bv = e0.Type.AsBitVectorType;
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
        wFirstArg.Append(TrExpr(e0, inLetExprBody, wStmts));
        wr.Append(TrExpr(e1, inLetExprBody, wStmts));
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
        return "Go__" + decl.CompileName;
      } else {
        return Capitalize(decl.CompileName);
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
        return IdProtect(udt.CompileName);
      } else {
        return UserDefinedTypeName(cl, full, member);
      }
    }

    private string UserDefinedTypeName(TopLevelDecl cl, bool full, MemberDecl/*?*/ member = null) {
      if (IsExternMemberOfExternModule(member, cl)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.EnclosingModuleDefinition.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(cl.EnclosingModuleDefinition.CompileName);
      } else {
        if (cl.IsExtern(out var qual, out _)) {
          // No need to take into account the second argument to extern, since
          // it'll already be cl.CompileName
          if (qual == null) {
            qual = cl.EnclosingModuleDefinition.CompileName;
          }
          // Don't use IdName since that'll capitalize, which is unhelpful for
          // built-in types
          return qual + (qual == "" ? "" : ".") + cl.CompileName;
        } else if (!full || cl.EnclosingModuleDefinition.IsDefaultModule || this.ModuleName == cl.EnclosingModuleDefinition.CompileName) {
          return IdName(cl);
        } else {
          return cl.EnclosingModuleDefinition.CompileName + "." + IdName(cl);
        }
      }
    }

    private bool IsExternMemberOfExternModule(MemberDecl/*?*/ member, TopLevelDecl cl) {
      return member != null && cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cdecl.EnclosingModuleDefinition.Attributes, "extern") && member.IsExtern(out _, out _);
    }

    protected override ICanRender EmitThis() {
      return new LineSegment("_this");
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
      wr.Append(TrExpr(guard, inLetExprBody, wStmts));
      wr.Write(" { return ");
      var wBranch = EmitCoercionIfNecessary(thn.Type, resultType, thn.tok, wr);
      wBranch.Append(TrExpr(thn, inLetExprBody, wStmts));
      wr.Write(" }; return ");
      wBranch = EmitCoercionIfNecessary(els.Type, resultType, thn.tok, wr);
      wBranch.Append(TrExpr(els, inLetExprBody, wStmts));
      wr.Write(" })() ");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, ConcreteSyntaxTree wr) {
      var ctorName = ctor.CompileName;
      var companionName = TypeName_Companion(dt, wr, dt.tok);

      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.TupleOf({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate: Companion_Dt_.CreateCtor(args)
        wr.Write("{0}.{1}({2})", companionName, FormatDatatypeConstructorName(ctorName), arguments);
      } else {
        // Co-recursive call
        // Generate:  Companion_Dt_.LazyDt(func () Dt => Companion_Dt_.CreateCtor(args))
        wr.Write("{0}.{1}(func () {2} ", companionName, FormatLazyConstructorName(dt.CompileName),
          TypeName(UserDefinedType.FromTopLevelDecl(dt.tok, dt), wr, dt.tok));
        wr.Write("{{ return {0}.{1}({2}) }}", companionName, FormatDatatypeConstructorName(ctorName), arguments);
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
          compiledName = string.Format("Len({0})", idParam == null ? 0 : (int)idParam);
          if (id == SpecialField.ID.ArrayLengthInt) {
            postString = ".Int()";
          }
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
      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(member);
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
            wr.Write(".{0}()", FormatDatatypeDestructorName(dtor.CompileName));
          }
        });
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        return SimpleLvalue(wr => {
          wr = EmitCoercionIfNecessary(sf.Type, expectedType, Token.NoToken, wr);
          obj(wr);
          string compiledName;
          GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out compiledName, out _, out _);
          if (compiledName.Length != 0) {
            wr.Write(".{0}", Capitalize(compiledName));
          } else {
            // this member selection is handled by some kind of enclosing function call, so nothing to do here
          }
        });
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
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
          EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), fn.tok, suffixWr, ref suffixSep);
          if (additionalCustomParameter != null) {
            suffixWr.Write("{0}{1}", suffixSep, additionalCustomParameter);
            suffixSep = ", ";
          }
          // Write the prefix and the rest of the suffix
          var prefixWr = new ConcreteSyntaxTree();
          var prefixSep = "";
          prefixWr.Write("func (");
          foreach (var arg in fn.Formals) {
            if (!arg.IsGhost) {
              var name = idGenerator.FreshId("_eta");
              var ty = arg.Type.Subst(typeMap);
              prefixWr.Write($"{prefixSep}{name} {TypeName(ty, prefixWr, arg.tok)}");
              suffixWr.Write("{0}{1}", suffixSep, name);
              suffixSep = ", ";
              prefixSep = ", ";
            }
          }
          var resultType = fn.ResultType.Subst(typeMap);
          prefixWr.Write(") {0} {{ return ", TypeName(resultType, prefixWr, fn.tok));
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
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w);
            w.Write(")");
          });
        } else if (NeedsCustomReceiver(member) && !(member.EnclosingClass is TraitDecl)) {
          // instance const in a newtype
          Contract.Assert(typeArgs.Count == 0);
          lvalue = SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            obj(w);
            w.Write(")");
          });
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          lvalue = SuffixLvalue(obj, $"._{member.CompileName}");
        } else if (internalAccess) {
          lvalue = SuffixLvalue(obj, $".{IdName(member)}");
        } else if (member is ConstantField) {
          lvalue = SimpleLvalue(w => {
            obj(w);
            w.Write(".{0}(", IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w);
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

    // TODO We might be able to be more consistent about whether indices are ints or Ints and avoid this
    private static string IntOfAny(string i) {
      return string.Format("_dafny.IntOfAny({0})", i);
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      wr = EmitCoercionIfNecessary(null, elmtType, Token.NoToken, wr);
      wr.Write("*(");
      var w = wr.Fork();
      wr.Write(".Index({0}))", Util.Comma(indices, IntOfAny));
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      wr = EmitCoercionIfNecessary(null, elmtType, Token.NoToken, wr);
      wr.Write("(*");
      var w = wr.Fork();
      wr.Write(".Index(");
      var sep = "";
      foreach (var index in indices) {
        wr.Write(sep);
        if (!index.Type.IsIntegerType) {
          wr.Write("_dafny.IntOfAny");
        }
        // No need for IntOfAny; things coming from user code are presumed Ints
        TrParenExpr(index, wr, inLetExprBody, wStmts);
        sep = ", ";
      }
      wr.Write("))");
      return w;
    }

    protected override ILvalue EmitArraySelectAsLvalue(string array, List<string> indices, Type elmtType) {
      return SimpleLvalue(wr =>
        wr.Write("*({0}.Index({1}))", array, Util.Comma(indices, IntOfAny))
      );
    }

    protected override ConcreteSyntaxTree EmitArrayUpdate(List<string> indices, string rhs, Type elmtType, ConcreteSyntaxTree wr) {
      wr.Write("*(");
      var w = wr.Fork();
      wr.Write(".Index({0})) = {1}", Util.Comma(indices, IntOfAny), rhs);
      return w;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (expr is LiteralExpr lit) {
        wr.Write(lit.Value.ToString());
      } else {
        TrParenExpr(expr, wr, inLetExprBody, wStmts);
        if (AsNativeType(expr.Type) == null) {
          wr.Write(".Int()");
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var type = source.Type.NormalizeExpand();
      if (type is SeqType seqType) {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Index(");
        TrExprToBigInt(index, wr, inLetExprBody);
        wr.Write(").({0})", TypeName(seqType.Arg, wr, null));
      } else if (type is MultiSetType) {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Multiplicity(");
        wr.Append(TrExpr(index, inLetExprBody, wStmts));
        wr.Write(")");
      } else {
        Contract.Assert(type is MapType);
        // map or imap
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Get(");
        wr.Append(TrExpr(index, inLetExprBody, wStmts));
        wr.Write(").({0})", TypeName(((MapType)type).Range, wr, null));
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitIndexCollectionUpdate(out var wSource, out var wIndex, out var wValue, wr, false);
      TrParenExpr(source, wSource, inLetExprBody, wSource);
      if (source.Type.AsSeqType != null) {
        TrExprToBigInt(index, wIndex, inLetExprBody);
      } else {
        wIndex.Append(TrExpr(index, inLetExprBody, wSource));
      }
      wValue.Append(TrExpr(value, inLetExprBody, wSource));
    }

    protected override void EmitIndexCollectionUpdate(out ConcreteSyntaxTree wSource, out ConcreteSyntaxTree wIndex, out ConcreteSyntaxTree wValue, ConcreteSyntaxTree wr, bool nativeIndex) {
      wSource = wr.Fork();
      wr.Write(nativeIndex ? ".UpdateInt(" : ".Update(");
      wIndex = wr.Fork();
      wr.Write(", ");
      wValue = wr.Fork();
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write(fromArray ? ".RangeToSeq(" : ".Subseq(");

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
    }

    void TrExprToBigInt(Expression e, ConcreteSyntaxTree wr, bool inLetExprBody) {
      var wStmts = wr.Fork();
      var nativeType = AsNativeType(e.Type);
      if (nativeType != null) {
        switch (nativeType.Sel) {
          case NativeType.Selection.Byte:
            wr.Write("_dafny.IntOfUint8(");
            break;
          case NativeType.Selection.UShort:
            wr.Write("_dafny.IntOfUint16(");
            break;
          case NativeType.Selection.UInt:
            wr.Write("_dafny.IntOfUint32(");
            break;
          case NativeType.Selection.ULong:
            wr.Write("_dafny.IntOfUint64(");
            break;
          case NativeType.Selection.SByte:
            wr.Write("_dafny.IntOfInt8(");
            break;
          case NativeType.Selection.Short:
            wr.Write("_dafny.IntOfInt16(");
            break;
          case NativeType.Selection.Int:
            wr.Write("_dafny.IntOfInt32(");
            break;
          case NativeType.Selection.Long:
            wr.Write("_dafny.IntOfInt64(");
            break;
          default:
            throw new cce.UnreachableException();  // unexpected nativeType.Selection value
        }
      }

      TrParenExpr(e, wr, inLetExprBody, wStmts);

      if (nativeType != null) {
        wr.Write(")");
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("_dafny.SeqCreate(");
      wr.Append(TrExpr(expr.N, inLetExprBody, wStmts));
      wr.Write(", ");
      var fromType = (ArrowType)expr.Initializer.Type.NormalizeExpand();
      var atd = (ArrowTypeDecl)fromType.ResolvedClass;
      var tParam = new UserDefinedType(expr.tok, new TypeParameter(expr.tok, "X", TypeParameter.TPVarianceSyntax.NonVariant_Strict));
      var toType = new ArrowType(expr.tok, atd, new List<Type>() { Type.Int }, tParam);
      var initWr = EmitCoercionIfNecessary(fromType, toType, expr.tok, wr);
      initWr.Append(TrExpr(expr.Initializer, inLetExprBody, wStmts));
      wr.Write(")");
      if (fromType.Result.IsCharType && !UnicodeCharEnabled) {
        // Tag this sequence as being a string at runtime,
        // but only if --unicode-char is false.
        // See "Printing strings and characters" in docs/Compilation/StringsAndChars.md.
        wr.Write(".SetString()");
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var eeType = expr.E.Type.NormalizeExpand();
      if (eeType is SeqType) {
        TrParenExpr("_dafny.MultiSetFromSeq", expr.E, wr, inLetExprBody, wStmts);
      } else if (eeType is SetType) {
        TrParenExpr("_dafny.MultiSetFromSet", expr.E, wr, inLetExprBody, wStmts);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function, List<Expression> arguments,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type type, IToken tok, bool inLetExprBody, ConcreteSyntaxTree wr,
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
      wr.Write("{0}.{1}()", source, FormatDatatypeConstructorCheckName(ctor.CompileName));
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
        wr.Write(source);
      } else if (ctor.EnclosingDatatype is TupleTypeDecl tupleTypeDecl) {
        Contract.Assert(tupleTypeDecl.NonGhostDims != 1); // such a tuple is an erasable-wrapper type, handled above
        wr.Write("(*({0}).IndexInt({1})).({2})", source, formalNonGhostIndex, TypeName(typeArgs[formalNonGhostIndex], wr, Token.NoToken));
      } else {
        var dtorName = DatatypeFieldName(dtor, formalNonGhostIndex);
        wr = EmitCoercionIfNecessary(from: dtor.Type, to: bvType, tok: dtor.tok, wr: wr);
        wr.Write("{0}.Get().({1}).{2}", source, TypeName_Constructor(ctor, wr), dtorName);
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
      Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      wr.Write("func (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1} {2}", i == 0 ? "" : ", ", inNames[i], TypeName(inTypes[i], wr, tok));
      }
      var w = wr.NewExprBlock(") {0}", TypeName(resultType, wr, tok));
      return w;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
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

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var w = wr.NewBigExprBlock("func () " + TypeName(resultType, wr, resultTok), "()");
      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
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
          TrParenExpr(expr, wr, inLetExprBody, wStmts);
          wr.Write(".Cardinality()");
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    private bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null ||
             (t.NormalizeExpand() is UserDefinedType udt && !t.IsArrowType && !t.IsTraitType && udt.ResolvedClass is ClassDecl);
    }

    private bool IsOrderedByCmp(Type t) {
      return t.IsIntegerType || t.IsRealType || t.IsBigOrdinalType || (t.IsBitVectorType && t.AsBitVectorType.NativeType == null) || (t.AsNewtype is NewtypeDecl nt && nt.NativeType == null);
    }

    private bool IsComparedByEquals(Type t) {
      return t.IsArrayType || t.IsIndDatatype || t.NormalizeExpand() is CollectionType;
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

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
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (!EqualsUpToParameters(eqType, DatatypeWrapperEraser.SimplifyType(e1.Type))) {
              staticCallString = "_dafny.AreEqual";
            } else if (IsOrderedByCmp(eqType)) {
              callString = "Cmp";
              postOpString = " == 0";
            } else if (IsComparedByEquals(eqType)) {
              callString = "Equals";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "==";
            } else {
              staticCallString = "_dafny.AreEqual";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
              postOpString = "/* handle */";
            } else if (!EqualsUpToParameters(eqType, DatatypeWrapperEraser.SimplifyType(e1.Type))) {
              preOpString = "!";
              staticCallString = "_dafny.AreEqual";
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
              staticCallString = "_dafny.AreEqual";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " < 0";
          } else {
            opString = "<";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Le:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " <= 0";
          } else {
            opString = "<=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " >= 0";
          } else {
            opString = ">=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " > 0";
          } else {
            opString = ">";
          }
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (AsNativeType(resultType) != null) {
            opString = "<<";
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            if (AsNativeType(e1.Type) != null) {
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
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            if (AsNativeType(e1.Type) != null) {
              callString = "Rsh(_dafny.IntOfUint64(uint64";
              postOpString = "))";
            } else {
              callString = "Rsh";
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.IsBitVectorType) {
            truncateResult = true;
          }
          if (resultType.IsCharType || AsNativeType(resultType) != null) {
            opString = "+";
          } else {
            callString = "Plus";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.IsBitVectorType) {
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
          if (resultType.IsBitVectorType) {
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
        case BinaryExpr.ResolvedOpcode.SeqEq:
          callString = "Equals"; break;
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
          callString = "IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "Concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "Contains"; reverseArguments = true; break;

        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments, out truncateResult, out convertE1_to_int,
            errorWr);
          break;
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("{0}.Cmp(_dafny.Zero) == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (e.ToType.Equals(e.E.Type)) {
        TrParenExpr(e.E, wr, inLetExprBody, wStmts);
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType || e.E.Type.IsBigOrdinalType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("_dafny.RealOfFrac(");
          ConcreteSyntaxTree w;
          if (e.E.Type.IsCharType) {
            wr.Write("_dafny.IntOfInt32(rune");
            w = wr.Fork();
            wr.Write(")");
          } else if (AsNativeType(e.E.Type) is NativeType nt) {
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(nt)));
            w = wr.Fork();
            wr.Write(")");
          } else {
            w = wr;
          }
          TrParenExpr(e.E, w, inLetExprBody, wStmts);
          wr.Write(", _dafny.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write($"{CharTypeName}(");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          if (AsNativeType(e.E.Type) == null) {
            wr.Write(".Int32()");
          }
          wr.Write(")");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            wr.Write(GetNativeTypeName(toNative));
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("_dafny.IntOfInt32(rune(");
              wr.Append(TrExpr(e.E, inLetExprBody, wStmts));
              wr.Write("))");
            } else {
              // char -> native
              wr.Write(GetNativeTypeName(toNative));
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            wr.Append(TrExpr(e.E, inLetExprBody, wStmts));
          } else if (fromNative != null) {
            Contract.Assert(toNative == null); // follows from other checks
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(fromNative)));
            wr.Append(TrExpr(e.E, inLetExprBody, wStmts));
            wr.Write(')');
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("{0}({1})", GetNativeTypeName(toNative), literal);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(u.E, wr, inLetExprBody, wStmts);
              wr.Write(".CardinalityInt())");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(m.Obj, wr, inLetExprBody, wStmts);
              wr.Write(".LenInt(0))");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
              wr.Write(".{0}()", Capitalize(GetNativeTypeName(toNative)));
            }
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Append(TrExpr(e.E, inLetExprBody, wStmts));
        } else if (e.ToType.IsCharType) {
          wr.Write($"{CharTypeName}(");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".Int().Int32())");
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".Int()");
          if (AsNativeType(e.ToType) is NativeType nt) {
            wr.Write(".{0}()", Capitalize(GetNativeTypeName(nt)));
          }
        }
      } else {
        Contract.Assert(false, $"not implemented for go: {e.E.Type} -> {e.ToType}");
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      Contract.Requires(fromType.IsRefType);
      Contract.Requires(toType.IsRefType);

      if (!fromType.IsNonNullRefType) {
        if (toType.IsNonNullRefType) {
          wr.Write($"!_dafny.IsDafnyNull({localName}) && ");
        } else {
          wr.Write($"_dafny.IsDafnyNull({localName}) || (");
        }
      }

      if (fromType.IsSubtypeOf(toType, true, true)) {
        wr.Write("true");
      } else if (toType.IsTraitType) {
        wr.Write($"_dafny.InstanceOfTrait({localName}.(_dafny.TraitOffspring), {TypeName_Companion(toType.AsTraitType, wr, tok)}.TraitID_)");
      } else {
        wr.Write($"_dafny.InstanceOf({localName}, ({TypeName(toType, wr, tok)})(nil))");
      }

      var udtTo = (UserDefinedType)toType.NormalizeExpandKeepConstraints();
      if (udtTo.ResolvedClass is SubsetTypeDecl && !(udtTo.ResolvedClass is NonNullTypeDecl)) {
        // TODO: test constraints
        throw new UnsupportedFeatureException(tok, Feature.SubsetTypeTests);
      }

      if (!fromType.IsNonNullRefType && !toType.IsNonNullRefType) {
        wr.Write(")");
      }
    }

    private static bool EqualsUpToParameters(Type type1, Type type2) {
      // TODO Consider whether Type.SameHead should return true in this case
      return Type.SameHead(type1, type2) || (type1.IsArrayType && type1.IsArrayType);
    }

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, IToken tok, ConcreteSyntaxTree wr) {
      if (to == null) {
        return wr;
      }

      from = from == null ? null : DatatypeWrapperEraser.SimplifyType(from);
      to = DatatypeWrapperEraser.SimplifyType(to);
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
      } else if (from != null && from.IsSubtypeOf(to, true, true)) {
        // upcast
        return wr;
      } else if (from == null || from.IsTypeParameter || to.IsSubtypeOf(from, true, true)) {
        // downcast (allowed?) or implicit cast from parameter
        if (to.IsObjectQ || to.IsObject) {
          // a cast to interface{} can be omitted
          return wr;
        } else if (to.IsTraitType) {
          wr.Write("{0}.CastTo_(", TypeName_Companion(to.AsTraitType, wr, tok));
          var w = wr.Fork();
          wr.Write(")");
          return w;
        } else {
          var w = wr.Fork();
          wr.Write(".({0})", TypeName(to, wr, tok));
          return w;
        }
      } else {
        // It's unclear to me whether it's possible to hit this case with a valid Dafny program,
        // so I'm not using UnsupportedFeatureError for now.
        Error(tok, "Cannot convert from {0} to {1}", wr, from, to);
        return wr;
      }
    }

    protected override ConcreteSyntaxTree EmitCoercionToNativeForm(Type from, IToken tok, ConcreteSyntaxTree wr) {
      // Don't expand!  We want to distinguish string from seq<char> here
      from = from.Normalize();
      if (from is UserDefinedType udt && udt.Name == "string") {
        wr.Write('(');
        var w = wr.Fork();
        wr.Write(").String()");
        return w;
      } else {
        return wr;
      }
    }

    protected override ConcreteSyntaxTree EmitCoercionFromNativeForm(Type to, IToken tok, ConcreteSyntaxTree wr) {
      // Don't expand! We want to distinguish string from seq<char> here
      to = to.Normalize();
      if (to is UserDefinedType udt && udt.Name == "string") {
        wr.Write("_dafny.SeqOfString(");
        var w = wr.Fork();
        wr.Write(")");
        return w;
      } else {
        return wr;
      }
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

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
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
      TrExprList(elements, wr, inLetExprBody, wStmts, type: ct.TypeArgs[0]);
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("_dafny.NewMapBuilder()");
      foreach (ExpressionPair p in elements) {
        wr.Write(".Add(");
        wr.Append(TrExpr(p.A, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(TrExpr(p.B, inLetExprBody, wStmts));
        wr.Write(')');
      }
      wr.Write(".ToMap()");
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
      wr.Append(TrExpr(elmt, inLetExprBody, wStmts));
      wr.WriteLine(")");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("{0}.Add(", collName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      wr.Append(TrExpr(term, inLetExprBody, wStmts));
      wr.WriteLine(")");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      if (ct is SetType) {
        return collName + ".ToSet()";
      } else {
        Contract.Assert(ct is MapType);
        return collName + ".ToMap()";
      }
    }

    protected override Type EmitIntegerRange(Type type, out ConcreteSyntaxTree wLo, out ConcreteSyntaxTree wHi, ConcreteSyntaxTree wr) {
      Type result;
      if (AsNativeType(type) != null) {
        wr.Write("{0}.IntegerRange(", TypeName_Companion(type.AsNewtype, wr, tok: Token.NoToken));
        result = type;
      } else {
        wr.Write("_dafny.IntegerRange(");
        result = new IntType();
      }
      wLo = wr.Fork();
      wr.Write(", ");
      wHi = wr.Fork();
      wr.Write(')');
      return result;
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody, wStmts);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var funcBlock = wr.NewBlock("func()", close: BlockStyle.Brace);
      var deferBlock = funcBlock.NewBlock("defer func()", close: BlockStyle.Brace);
      var ifRecoverBlock = deferBlock.NewBlock("if r := recover(); r != nil");
      ifRecoverBlock.WriteLine($"var {haltMessageVarName} = _dafny.SeqOfString(r.(string))");
      TrStmt(recoveryBody, ifRecoverBlock);
      funcBlock.WriteLine("()");
      TrStmt(body, funcBlock);
      wr.WriteLine("()");
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (runAfterCompile) {
        Contract.Assert(callToMain != null);  // this is part of the contract of CompileTargetProgram
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'go run'
        // will run the program.
        return true;
      } else {
        // compile now
        return SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames, outputWriter, callToMain != null, run: false);
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      return SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames, outputWriter, hasMain: true, run: true);
    }

    private bool SendToNewGoProcess(string dafnyProgramName, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      TextWriter outputWriter, bool hasMain, bool run) {
      Contract.Requires(targetFilename != null);

      foreach (var otherFileName in otherFileNames) {
        if (Path.GetExtension(otherFileName) != ".go") {
          outputWriter.WriteLine("Unrecognized file as extra input for Go compilation: {0}", otherFileName);
          return false;
        }

        if (!CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName, outputWriter: outputWriter)) {
          return false;
        }
      }

      List<string> goArgs = new();
      if (run) {
        goArgs.Add("run");
      } else {
        string output;
        var outputToFile = !DafnyOptions.O.RunAfterCompile;

        if (outputToFile) {
          string extension;
          if (hasMain) {
            switch (Environment.OSVersion.Platform) {
              case PlatformID.Unix:
              case PlatformID.MacOSX:
              case (PlatformID)128: // early Mono
                extension = null;
                break;
              default:
                extension = "exe";
                break;
            }
          } else {
            extension = "a";
          }
          output = Path.ChangeExtension(dafnyProgramName, extension);
        } else {
          switch (Environment.OSVersion.Platform) {
            case PlatformID.Unix:
            case PlatformID.MacOSX:
            case (PlatformID)128: // early Mono
              output = "/dev/null";
              break;
            default:
              output = "NUL";
              break;
          }
        }

        goArgs.Add("build");
        goArgs.Add("-o");
        goArgs.Add(output);
      }

      goArgs.Add(targetFilename);
      goArgs.AddRange(DafnyOptions.O.MainArgs);

      var psi = PrepareProcessStartInfo("go", goArgs);

      psi.EnvironmentVariables["GOPATH"] = GoPath(targetFilename);
      // Dafny compiles to the old Go package system, whereas Go has moved on to a module
      // system. Until Dafny's Go compiler catches up, the GO111MODULE variable has to be set.
      psi.EnvironmentVariables["GO111MODULE"] = "auto";

      return 0 == RunProcess(psi, outputWriter);
    }

    static string GoPath(string filename) {
      var dirName = Path.GetDirectoryName(Path.GetDirectoryName(filename));

      Contract.Assert(dirName != null);

      // Filename is Foo-go/src/Foo.go, so go two directories up
      return Path.GetFullPath(dirName);
    }

    static bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
      // Grossly, we need to look in the file to figure out where to put it
      var pkgName = FindPackageName(externFilename);
      if (pkgName == null) {
        outputWriter.WriteLine("Unable to determine package name: {0}", externFilename);
        return false;
      }
      if (pkgName.StartsWith("_")) {
        // Check this here because otherwise Go acts like the package simply doesn't exist, which is confusing
        outputWriter.WriteLine("Go packages can't start with underscores: {0}", pkgName);
        return false;
      }

      var mainDir = Path.GetDirectoryName(mainProgram);

      Contract.Assert(mainDir != null);

      var tgtDir = Path.Combine(mainDir, pkgName);
      var tgtFilename = Path.Combine(tgtDir, pkgName + ".go");

      Directory.CreateDirectory(tgtDir);
      File.Copy(externFilename, tgtFilename, overwrite: true);

      string relTgtFilename;
      var cwd = Directory.GetCurrentDirectory();
      if (tgtFilename.StartsWith(cwd)) {
        relTgtFilename = tgtFilename.Substring(cwd.Length + 1); // chop off relative path and '/'
      } else {
        relTgtFilename = tgtFilename;
      }
      if (DafnyOptions.O.CompileVerbose) {
        outputWriter.WriteLine("Additional input {0} copied to {1}", externFilename, relTgtFilename);
      }
      return true;
    }

    private static string FindPackageName(string externFilename) {
      using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
      while (rd.ReadLine() is string line) {
        var match = PackageLine.Match(line);
        if (match.Success) {
          return match.Groups[1].Value;
        }
      }
      return null;
    }

    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*$");
  }
}
