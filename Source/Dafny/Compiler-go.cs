//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.ComponentModel;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class GoCompiler : Compiler {
    public GoCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "Go";

    private readonly List<Import> Imports = new List<Import>(StandardImports);
    private string ModuleName;
    private TargetWriter RootImportWriter;
    private TargetWriter RootImportDummyWriter;

    private string MainModuleName;
    private static List<Import> StandardImports =
      new List<Import> {
        new Import { Name = "_dafny", Path = "dafny" },
      };
    private static string DummyTypeName = "Dummy__";

    private struct Import {
      public string Name, Path;
      public bool SuppressDummy;
    }

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into Go", program.Name);

      ModuleName = MainModuleName = HasMain(program, out _) ? "main" : Path.GetFileNameWithoutExtension(program.Name);

      wr.WriteLine("package {0}", ModuleName);
      wr.WriteLine();
      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter, out RootImportDummyWriter);
    }

    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
      var rt = wr.NewFile("dafny/dafny.go");
      ReadRuntimeSystem("DafnyRuntime.go", rt);
    }

    void EmitModuleHeader(TargetWriter wr) {
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

    void EmitImports(TargetWriter wr, out TargetWriter importWriter, out TargetWriter importDummyWriter) {
      wr.WriteLine("import (");
      importWriter = wr.ForkSection(true);
      wr.WriteLine(")");
      importDummyWriter = wr.ForkSection();

      foreach (var import in Imports) {
        EmitImport(import, importWriter, importDummyWriter);
      }
    }

    public override void EmitCallToMain(Method mainMethod, TargetWriter wr) {
      var companion = TypeName_Companion(mainMethod.EnclosingClass as ClassDecl, wr, mainMethod.tok);

      var wBody = wr.NewNamedBlock("func main()");
      wBody.WriteLine("{0}.{1}()", companion, IdName(mainMethod));
    }

    TargetWriter CreateDescribedSection(string desc, TargetWriter wr, params object[] args) {
      var body = wr.NewSection();
      var str = string.Format(desc, args);
      body.WriteLine("// Definition of {0}", str);
      wr.WriteLine("// End of {0}", str);
      return body;
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = ((GoCompiler.ClassWriter) cw).ConcreteMethodWriter;
      return wr.NewNamedBlock("func (_this * {0}) Main()", FormatCompanionTypeName(((GoCompiler.ClassWriter) cw).ClassName));
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, TargetWriter wr) {
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
          Error(Bpl.Token.NoToken, "Cannot have a package name with only underscores: {0}", wr, pkgName);
          return wr;
        }
        while (pkgName.StartsWith("_")) {
          pkgName = pkgName.Substring(1) + "_";
        }
      }

      var import = new Import{ Name=moduleName, Path=pkgName };
      if (isExtern) {
        // Allow the library name to be "" to import built-in things like the error type
        if (pkgName != "") {
          import.SuppressDummy = true;
          AddImport(import);
        }
        return new TargetWriter(); // ignore contents of extern module
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

    private void EmitImport(Import import, TargetWriter importWriter, TargetWriter importDummyWriter) {
      var id = IdProtect(import.Name);
      var path = import.Path;

      importWriter.WriteLine("{0} \"{1}\"", id, path);

      if (!import.SuppressDummy) {
        importDummyWriter.WriteLine("var _ {0}.{1}", id, DummyTypeName);
      }
    }

    protected override string GetHelperModuleName() => "_dafny";

    protected override IClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      return CreateClass(name, isExtern, fullPrintName, typeParameters, superClasses, tok, wr, includeRtd: true, includeEquals: true);
    }

    // TODO Consider splitting this into two functions; most things seem to be
    // passing includeRtd: false and includeEquals: false.
    private GoCompiler.ClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr, bool includeRtd, bool includeEquals) {
      //
      // The system for getting traits and inheritance to work is a little
      // fiddly.  There is no inheritance in Go.  You can, however, *embed* the
      // trait struct in the class's struct.  This gives you some things---the
      // class responds to the trait's methods, for instance, and the trait's
      // fields get added in.  But instead of an upcast, you have to project
      // the trait struct out, which would lose the ability for a method
      // invocation to get back the whole object.  (If traits had only methods,
      // we could use Go interfaces, but fields make life harder.)
      //
      // So in order to be able to cast to a trait, whose instance methods
      // should be invoked with the original object, every trait struct embeds
      // an interface type with its abstract methods.  Effectively this is a
      // back pointer to the whole object, imbued with a vtable.  Since the
      // trait struct embeds the interface, it's a receiver for the interface
      // (i.e. the methods can be invoked on the trait struct).
      //
      // It sounds like the class embeds each trait, each of which embeds the
      // class!  Crucially, classes all use pointer receivers, so in embedding
      // an interface, the trait struct actually embeds a pointer, so it all
      // ends up tied up with a bow.
      //
      // There are two sources of complexity here that impact the compiler in
      // general:
      //
      //   1. Upcasts are explicit.  This is why EmitCoercionIfNecessary() came
      //      to be.  (It would be handy if our IR included upcasts rather than
      //      leaving the subtyping implicit, but there aren't that many places
      //      where coercions are necessary---really just function calls and
      //      assignments to variables.)
      //   2. We need to wire up the trait structs with their back pointers
      //      whenever an object is created.  This is taken care of in the
      //      initializer (New_Class_), so we just need to make sure all object
      //      creation goes through there.
      //
      // type Class struct {
      //   Trait0
      //   Trait1
      //   ...
      //   Type0 _dafny.Type
      //   Type1 _dafny.Type
      //   ...
      //   Field0 type0
      //   Field1 type1
      //   ...
      // }
      //
      // type CompanionStruct_Class_ struct {
      //   *CompanionStruct_Trait0
      //   *CompanionStruct_Trait1
      //   StaticField0 type0
      //   StaticField1 type1
      //   ...
      // }
      //
      // var Companion_Class_ = CompanionStruct_Class_{
      //   &Companion_Trait0,
      //   &Companion_Trait1,
      //   StaticField1: ...,
      //   StaticField2: ...,
      // }
      //
      // func New_Class_(Type0 Dafny.Type, Type1 Dafny.Type) *Class {
      //   _this := Class{}
      //
      //   // Have to do it this way because some default values (namely type
      //   // parameters) assume that _this points to the current value
      //   _this.Type0 = Type0
      //   _this.Type1 = Type1
      //   _this.Trait0 = New_Trait0_()
      //   _this.Trait1 = New_Trait1_()
      //   _this.Field0 = ...
      //   _this.Field1 = ...
      //
      //   _this.Trait0.Iface_Trait0 = &_this
      //   _this.Trait1.Iface_Trait1 = &_this
      //   return &_this
      // }
      //
      // func (_this *Class) InstanceMethod(param0 type0, ...) returnType {
      //   ...
      //   _this.Trait0.TraitField0 // access field from trait
      //   var traitVar Trait1 = _this.Trait1 // cast to trait
      //   _this.TraitMethod0() // can invoke trait method directly
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
      // func Type_Class_(Type0 _dafny.Type, Type1 _dafny.Type) _dafny.Type {
      //   return type_Class_{Type0, Type1}
      // }
      //
      // type type_Class_ struct{
      //   Type0 _dafny.Type
      //   Type1 _dafny.Type
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
        WriteRuntimeTypeDescriptorsFields(typeParameters, true, instanceFieldWriter, instanceFieldInitWriter, rtdParamWriter);
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
        w.WriteLine();
        BlockTargetWriter wDefault;
        CreateRTD(name, typeParameters, out wDefault, w);

        wDefault.WriteLine("return (*{0})(nil)", name);
      }

      var cw = new ClassWriter(this, name, isExtern, null, w, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);

      if (superClasses != null) {
        foreach (Type typ in superClasses) {
          cw.AddSuperType(typ, tok);
        }
      }
      return cw;
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      //
      // type Trait struct {
      //   Iface_Trait_ // see comments on CreateClass
      //   InstanceField0 type0
      //   ...
      // }
      //
      // type Iface_Trait_ interface {
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
      // func (_this *Trait) ConcreteInstanceMethod(...) ... {
      //   ...
      // }
      //
      // func (_this *companionStruct_Trait) StaticMethod(...) ... {
      //   ...
      // }
      //
      wr = CreateDescribedSection("trait {0}", wr, name);
      var instanceFieldWriter = wr.NewNamedBlock("type {0} struct", name);
      instanceFieldWriter.WriteLine(FormatTraitInterfaceName(name));
      var abstractMethodWriter = wr.NewNamedBlock("type {0} interface", FormatTraitInterfaceName(name));
      var concreteMethodWriter = wr.ForkSection();

      CreateInitializer(name, wr, out var instanceFieldInitWriter, out var traitInitWriter, rtdParamWriter:out _);

      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));

      var cw = new ClassWriter(this, name, isExtern, abstractMethodWriter, concreteMethodWriter, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);
      if (superClasses != null) {
        foreach (Type typ in superClasses) {
          cw.AddSuperType(typ, tok);
        }
      }
      return cw;
    }

    protected void CreateInitializer(string name, TargetWriter wr, out TargetWriter instanceFieldInitWriter, out TargetWriter traitInitWriter, out TargetWriter rtdParamWriter) {
      wr.Write("func {0}(", FormatInitializerName(name));
      rtdParamWriter = wr.Fork();
      var w = wr.NewNamedBlock(") *{0}", name);
      w.WriteLine("_this := {0}{{}}", name);

      w.WriteLine();
      instanceFieldInitWriter = w.ForkSection();
      traitInitWriter = w.ForkSection();
      w.WriteLine("return &_this");
    }

    protected override bool NeedsWrappersForInheritedFields => false;
    protected override bool SupportsProperties => false;

    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr) {
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
          cw.DeclareField(IdName(f), false, false, f.Type, f.tok, DefaultValue(f.Type, wr, f.tok));
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

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
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
      // // For uniformity with co-data types
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
      // func Type_Dt_(tyArg0 Type, tyArg1 Type, ...) _dafny.Type {
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

      Func<DatatypeCtor, string> structOfCtor = ctor =>
        string.Format("{0}{1}_{2}", dt is CoDatatypeDecl ? "*" : "", name, ctor.CompileName);

      // from here on, write everything into the new block created here:
      wr = CreateDescribedSection("{0} {1}", wr, dt is IndDatatypeDecl ? "data type" : "co-data type", name);

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

      foreach (var ctor in dt.Ctors) {
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

      if (dt.HasFinitePossibleValues) {
        wr.WriteLine();
        var wSingles = wr.NewNamedBlock("func (_ {0}) AllSingletonConstructors() _dafny.Iterator", companionTypeName);
        wSingles.WriteLine("i := -1");
        wSingles = wSingles.NewNamedBlock("return func() (interface{{}}, bool)");
        wSingles.WriteLine("i++");
        wSingles = wSingles.NewNamedBlock("switch i");
        var i = 0;
        foreach (var ctor in dt.Ctors) {
          wSingles.WriteLine("case {0}: return {1}.{2}(), true", i, FormatCompanionName(name), FormatDatatypeConstructorName(ctor.CompileName));
          i++;
        }
        wSingles.WriteLine("default: return {0}{{}}, false", name);
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              wr.WriteLine();
              var wDtor = wr.NewNamedBlock("func (_this {0}) {1}() {2}", name, FormatDatatypeDestructorName(arg.CompileName), TypeName(arg.Type, wr, arg.tok));
              var n = dtor.EnclosingCtors.Count;
              if (n == 1) {
                wDtor.WriteLine("return _this.Get().({0}).{1}", structOfCtor(dtor.EnclosingCtors[0]), DatatypeFieldName(arg));
              } else {
                wDtor = wDtor.NewBlock("switch data := _this.Get().(type)");
                for (int i = 0; i < n-1; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  wDtor.WriteLine("case {0}: return data.{1}", structOfCtor(ctor_i), DatatypeFieldName(arg));
                }
                Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n-1].CompileName);
                wDtor.WriteLine("default: return data.({0}).{1}", structOfCtor(dtor.EnclosingCtors[n-1]), DatatypeFieldName(arg));
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
        var needData = dt is IndDatatypeDecl && dt.Ctors.Exists(ctor => ctor.Formals.Exists(arg => !arg.IsGhost));
        w = w.NewNamedBlock("switch {0}_this.Get().(type)", needData ? "data := " : "");
        w.WriteLine("case nil: return \"null\"");
        foreach (var ctor in dt.Ctors) {
          var wCase = w.NewNamedBlock("case {0}:", structOfCtor(ctor));
          var nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
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
                wCase.Write("{0}_dafny.String(data.{1})", sep, DatatypeFieldName(arg, k));
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
          wDefault.WriteLine("return \"{0}.{1}.unexpected\"", dt.Module.CompileName, dt.CompileName);
        } else {
          wDefault.WriteLine("return \"<unexpected>\"");
        }
      }

      // Equals method
      {
        wr.WriteLine();
        var wEquals = wr.NewNamedBlock("func (_this {0}) Equals(other {0}) bool", name);
        // TODO: Way to implement shortcut check for address equality?
        var needData1 = dt.Ctors.Exists(ctor => ctor.Formals.Exists(arg => !arg.IsGhost));

        wEquals = wEquals.NewNamedBlock("switch {0}_this.Get().(type)", needData1 ? "data1 := " : "");
        foreach (var ctor in dt.Ctors) {
          var wCase = wEquals.NewNamedBlock("case {0}:", structOfCtor(ctor));

          var needData2 = ctor.Formals.Exists(arg => !arg.IsGhost);

          wCase.WriteLine("{0}, ok := other.Get().({1})", needData2 ? "data2" : "_", structOfCtor(ctor));
          wCase.Write("return ok");
          var k = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              wCase.Write(" && ");
              string nm = DatatypeFieldName(arg, k);
              if (IsDirectlyComparable(arg.Type)) {
                wCase.Write("data1.{0} == data2.{0}", nm);
              } else if (IsOrderedByCmp(arg.Type)) {
                wCase.Write("data1.{0}.Cmp(data2.{0}) == 0", nm);
              } else if (IsComparedByEquals(arg.Type)) {
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
        BlockTargetWriter wDefault;
        CreateRTD(name, usedTypeParams, out wDefault, wr);

        WriteRuntimeTypeDescriptorsLocals(usedTypeParams, true, wDefault);

        wDefault.Write("return ");
        DatatypeCtor defaultCtor;
        if (dt is IndDatatypeDecl idd) {
          defaultCtor = idd.DefaultCtor;
        } else {
          defaultCtor = dt.Ctors[0];
        }

        var arguments = new TargetWriter();
        string sep = "";
        foreach (var f in defaultCtor.Formals) {
          if (!f.IsGhost) {
            arguments.Write("{0}{1}", sep, DefaultValue(f.Type, wDefault, f.tok));
            sep = ", ";
          }
        }
        EmitDatatypeValue(dt, defaultCtor, dt is CoDatatypeDecl, arguments.ToString(), wDefault);
        wDefault.WriteLine();
      }

      return new ClassWriter(this, name, dt.IsExtern(out _, out _), null, wr, wr, wr, wr, staticFieldWriter, staticFieldInitWriter);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr) {
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
        var retType = nt.NativeType != null ? GetNativeTypeName(nt.NativeType) : TypeName(nt.BaseType, w, nt.tok);
        var wWitness = w.NewNamedBlock("func (_this *{0}) Witness() {1}", FormatCompanionTypeName(IdName(nt)), retType);
        wWitness.Write("return ");
        if (nt.NativeType == null) {
          TrExpr(nt.Witness, wWitness, false);
        } else {
          TrParenExpr(nt.Witness, wWitness, false);
          wWitness.Write(".{0}()", Capitalize(GetNativeTypeName(nt.NativeType)));
        }
      }
      // RTD
      {
        CreateRTD(IdName(nt), null, out var wDefaultBody, wr);
        var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
        var d = TypeInitializationValue(udt, wr, nt.tok, false);
        wDefaultBody.WriteLine("return {0}", d);
      }
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr) {
      var cw = CreateClass(IdName(sst), false, null, sst.TypeArgs, null, null, wr, includeRtd: false, includeEquals: false);
      var w = cw.ConcreteMethodWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(sst.Witness, witness, false);
        DeclareField("Witness", false, true, true, sst.Rhs, sst.tok, witness.ToString(), cw.ClassName, cw.StaticFieldWriter, cw.StaticFieldInitWriter, cw.ConcreteMethodWriter);
      }
      // RTD
      {
        CreateRTD(IdName(sst), null, out var wDefaultBody, wr);
        var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
        var d = TypeInitializationValue(udt, wr, sst.tok, false);
        wDefaultBody.WriteLine("return {0}", d);
      }
    }

    private void CreateRTD(string typeName, List<TypeParameter>/*?*/ usedParams, out BlockTargetWriter wDefaultBody, TargetWriter wr) {
      if (usedParams == null) {
        usedParams = new List<TypeParameter>();
      }
      wr.Write("func {0}(", FormatRTDName(typeName));
      WriteRuntimeTypeDescriptorsFormals(usedParams, true, wr);
      var wTypeMethod = wr.NewBlock(") _dafny.Type");
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
        case NativeType.Selection.Number:
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
      public readonly TargetWriter/*?*/ AbstractMethodWriter, ConcreteMethodWriter, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter;
      public bool AnyInstanceFields { get; private set; } = false;

      public ClassWriter(GoCompiler compiler, string className, bool isExtern, TargetWriter abstractMethodWriter, TargetWriter concreteMethodWriter, TargetWriter instanceFieldWriter, TargetWriter instanceFieldInitWriter, TargetWriter traitInitWriter, TargetWriter staticFieldWriter, TargetWriter staticFieldInitWriter) {
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

      public TargetWriter FieldWriter(bool isStatic) {
        return isStatic ? StaticFieldWriter : InstanceFieldWriter;
      }

      public TargetWriter FieldInitWriter(bool isStatic) {
        return isStatic ? StaticFieldInitWriter : InstanceFieldInitWriter;
      }

      public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
        return Compiler.CreateMethod(m, createBody, ClassName, AbstractMethodWriter, ConcreteMethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, ClassName, AbstractMethodWriter, ConcreteMethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, member, ClassName, ConcreteMethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, member, name, out setterWriter, ConcreteMethodWriter);
      }
      public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
        // FIXME: This should probably be done in Compiler.DeclareField().
        // Should just have these delegate methods take the ClassWriter as an
        // argument.
        if (!isStatic) {
          AnyInstanceFields = true;
        }
        Compiler.DeclareField(name, IsExtern, isStatic, isConst, type, tok, rhs, ClassName, FieldWriter(isStatic), FieldInitWriter(isStatic), ConcreteMethodWriter);
      }
      public TextWriter/*?*/ ErrorWriter() => ConcreteMethodWriter;

      public void AddSuperType(Type superType, Bpl.IToken tok) {
        Compiler.AddSuperType(superType, tok, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter);
      }

      public void Finish() {
        Compiler.FinishClass(this);
      }
    }

    protected BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, string ownerName, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      return CreateSubroutine(IdName(m), m.TypeArgs, m.Ins, m.Outs, null, m.tok, m.IsStatic, m.IsTailRecursive, createBody, ownerName, m, abstractWriter, concreteWriter);
    }

    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, string ownerName, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      return CreateSubroutine(name, typeArgs, formals, new List<Formal>(), resultType, tok, isStatic, false, createBody, ownerName, member, abstractWriter, concreteWriter);
    }

    private BlockTargetWriter CreateSubroutine(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> inParams, List<Formal> outParams, Type/*?*/ resultType, Bpl.IToken tok, bool isStatic, bool isTailRecursive, bool createBody, string ownerName, MemberDecl member, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      var customReceiver = NeedsCustomReceiver(member);
      TargetWriter wr;
      if (createBody || abstractWriter == null) {
        wr = concreteWriter;
        string receiver = isStatic || customReceiver ? FormatCompanionTypeName(ownerName) : ownerName;
        if (member.EnclosingClass is DatatypeDecl) {
          wr.Write("func ({0} {1}) ", isStatic ? "_static" : "_this", receiver);
        } else {
          wr.Write("func ({0} *{1}) ", isStatic || customReceiver ? "_static" : "_this", receiver);
        }
      } else {
        wr = abstractWriter;
      }
      wr.Write("{0}(", name);
      var nTypes = WriteRuntimeTypeDescriptorsFormals(typeArgs, false, wr);
      if (customReceiver) {
        wr.Write("{0}_this {1}", nTypes != 0 ? ", " : "", TypeName(UserDefinedType.FromTopLevelDecl(tok, member.EnclosingClass), wr, tok));
      }
      var _ = WriteFormals(nTypes != 0 || customReceiver ? ", " : "", inParams, wr);
      wr.Write(")");

      // TODO: Maybe consider using named result parameters, since they're
      // actually close to how Dafny method outs work
      WriteOutTypes(outParams, resultType, wr, tok);

      if (createBody) {
        var w = wr.NewBlock("");

        if (isTailRecursive) {
          w.WriteLine("goto TAIL_CALL_START");
          w.WriteLine("TAIL_CALL_START:");
        }

        if (outParams.Any()) {
          var r = new TargetWriter(w.IndentLevel);
          EmitReturn(outParams, r);
          w.BodySuffix = r.ToString();
        }
        return w;
      } else {
        wr.WriteLine();
        return null;
      }
    }

    protected void WriteOutTypes(List<Formal> outParams, Type/*?*/ resultType, TargetWriter wr, Bpl.IToken tok) {
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
        wr.Write(Util.Comma(", ", outTypes, ty => TypeName(ty, wr, tok)));
        if (outTypes.Count > 1) {
          wr.Write(')');
        }
      }
    }

    void WriteRuntimeTypeDescriptorsFields(List<TypeParameter> typeParams, bool useAllTypeArgs, BlockTargetWriter wr, TargetWriter/*?*/ wInit, TargetWriter/*?*/ wParams) {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      var sep = "";
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          var name = FormatRTDName(tp.CompileName);

          wr.WriteLine("{0} _dafny.Type", name);

          if (wInit != null) {
            wInit.WriteLine("_this.{0} = {0}", name);
          }

          if (wParams != null) {
            wParams.Write("{0}{1} _dafny.Type", sep, name);
            sep = ", ";
          }
        }
      }
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write("{0}{1} _dafny.Type", prefix, FormatRTDName(tp.CompileName));
          prefix = ", ";
          c++;
        }
      }
      return c;
    }

    void WriteRuntimeTypeDescriptorsLocals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr) {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.WriteLine("{0} := _this.{0}", FormatRTDName(tp.CompileName));
          wr.WriteLine("_ = {0}", FormatRTDName(tp.CompileName));
        }
      }
    }

    protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals, Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr) {
      var sep = "";
      var c = 0;
      for (int i = 0; i < typeArgs.Count; i++) {
        var actual = typeArgs[i];
        var formal = formals[i];
        if (useAllTypeArgs || formal.Characteristics.MustSupportZeroInitialization) {
          wr.Write("{0}{1}", sep, RuntimeTypeDescriptor(actual, tok, wr));
          sep = ", ";
          c++;
        }
      }
      return c;
    }

    string RuntimeTypeDescriptor(Type type, Bpl.IToken tok, TextWriter wr, bool inInitializer = false) {
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);

      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as bool, since no particular type information is apparently needed for this type
        return "_dafny.BoolType";
      }

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
      } else if (xType.IsBuiltinArrowType) {

        return string.Format("_dafny.TypeWithDefault({0})", TypeInitializationValue(xType, wr, tok, false));
      } else if (xType.IsObjectQ) {
        return "_dafny.PointerType";
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        var tp = udt.ResolvedParam;
        if (tp != null) {
          return string.Format("{0}{1}", !inInitializer && tp.Parent is ClassDecl ? "_this." : "", FormatRTDName(tp.CompileName));
        }
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "_dafny.PointerType";
        } else if (cl is ArrayClassDecl) {
          return "_dafny.ArrayType";
        } else if (cl is ClassDecl || cl is DatatypeDecl) {
          var w = new TargetWriter();
          w.Write("{0}(", cl is TupleTypeDecl ? "_dafny.TupleType" : TypeName_RTD(xType, w, tok));
          List<TypeParameter> usedTypeFormals;
          List<Type> usedTypeArgs;
          if (cl is DatatypeDecl dt) {
            UsedTypeParameters(dt, udt.TypeArgs, out usedTypeFormals, out usedTypeArgs);
          } else {
            usedTypeArgs = udt.TypeArgs;
            usedTypeFormals = cl.TypeArgs;
          }
          EmitRuntimeTypeDescriptorsActuals(usedTypeArgs, usedTypeFormals, udt.tok, true, w);
          w.Write(")");
          return w.ToString();
        } else if (xType.IsNonNullRefType) {
          // this initializer shouldn't ever be needed; the compiler is expected to generate an error
          // sooner or later, , but it could be that the the compiler needs to
          // lay down some bits to please the C#'s compiler's different definite-assignment rules.
          return "_dafny.PointerType/*not used*/";
        } else {
          Contract.Assert(cl is NewtypeDecl || cl is SubsetTypeDecl);
          return TypeName_RTD(xType, wr, udt.tok) + "()";
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, string ownerName, TargetWriter wr) {
      // We don't use getters
      return createBody ? new TargetWriter().NewBlock("") : null;
    }

    protected BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, string ownerName, out TargetWriter setterWriter, TargetWriter wr) {
      // We don't use getter/setter pairs; we just embed the trait's fields.
      if (createBody) {
        var abyss = new TargetWriter();
        setterWriter = abyss;
        return abyss.NewBlock("");
      } else {
        setterWriter = null;
        return null;
      }
    }

    private void AddSuperType(Type superType, Bpl.IToken tok, TargetWriter instanceFieldWriter, TargetWriter instanceFieldInitWriter, TargetWriter traitInitWriter, TargetWriter staticFieldWriter, TargetWriter staticFieldInitWriter) {
      instanceFieldWriter.WriteLine("{0}", TypeName(superType, instanceFieldWriter, tok));

      var embed = UnqualifiedClassName(superType, instanceFieldInitWriter, tok);

      instanceFieldInitWriter.WriteLine("_this.{0} = {1}()", embed, TypeName_Initializer(superType, instanceFieldInitWriter, tok));

      if (superType.IsTraitType) {
        traitInitWriter.WriteLine("_this.{0}.{1} = &_this", embed, FormatTraitInterfaceName(embed));
      }

      staticFieldWriter.WriteLine("*{0}", TypeName_CompanionType(superType, staticFieldWriter, tok));

      staticFieldInitWriter.WriteLine("{0}: &{1},", FormatCompanionTypeName(embed), TypeName_Companion(superType, staticFieldInitWriter, tok, null));
    }

    private void FinishClass(GoCompiler.ClassWriter cw) {
      // Go gets weird about zero-length structs.  In particular, it likes to
      // make all pointers to a zero-length struct the same.  Irritatingly, this
      // forces us to waste space here.
      if (!cw.AnyInstanceFields) {
        cw.InstanceFieldWriter.WriteLine("dummy byte");
      }
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("goto TAIL_CALL_START");
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "interface {}";
      }

      if (xType is SpecialNativeType snt) {
        return snt.Name;
      } else if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "_dafny.Char";
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
        } else if (DafnyOptions.O.IronDafny &&
            !(xType is ArrowType) &&
            cl != null &&
            cl.Module != null &&
            !cl.Module.IsDefaultModule) {
          s = cl.FullCompileName;
        } else if (xType is ArrowType at) {
          return string.Format("func ({0}) {1}", Util.Comma(at.Args, arg => TypeName(arg, wr, tok)), TypeName(at.Result, wr, tok));
        } else if (cl is TupleTypeDecl) {
          return "_dafny.Tuple";
        } else if (udt.IsTypeParameter) {
          return "interface{}";
        }
        if (udt.IsDatatype) {
          // Don't return a pointer to the datatype because the datatype is
          // already represented using a pointer
          return IdProtect(s);
        } else if (udt.IsTraitType && udt.ResolvedClass.IsExtern(out _, out _)) {
          // To use an external interface, we need to have values of the
          // interface type, so we treat an extern trait as a plain interface
          // value, not a pointer (a Go interface value is basically a typed
          // pointer anyway).
          //
          // Also don't use IdProtect so that we can have it be a built-in
          // name like error.
          return s;
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

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok, bool inAutoInitContext) {
      // When returning nil, explicitly cast the nil so that type assertions work
      Func<string> nil = () => string.Format("({0})(nil)", TypeName(type, wr, tok));

      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "_dafny.Char('D')";
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
      } else if (xType is SeqType) {
        return "_dafny.EmptySeq";
      } else if (xType is MapType) {
        return "_dafny.EmptyMap";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization) {
          return nil();
        } else {
          var w = new TargetWriter(0, true);
          w = EmitCoercionIfNecessary(from:null, to:xType, tok:tok, wr:w);
          w.Write(RuntimeTypeDescriptor(udt, udt.tok, wr));
          w.Write(".Default()");
          return w.ToString();
        }
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_Companion(cl, wr, tok) + ".Witness()";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_Companion(type, wr, tok, null) + ".Witness()";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return nil();
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("func ({0}) {1} {{ return {2}; }}", Util.Comma(udt.TypeArgs.GetRange(0, udt.TypeArgs.Count-1), tp => TypeName(tp, wr, tok)), TypeName(udt.TypeArgs.Last(), wr, tok), rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            // non-null array type; we know how to initialize them
            return string.Format("_dafny.NewArrayWithValue({0}, {1})", TypeInitializationValue(xType.TypeArgs[0], wr, tok, inAutoInitContext), Util.Comma(arrayClass.Dims, d => string.Format("_dafny.IntOf({0})", d)));
          } else {
            return nil();
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return nil();
        }
      } else if (cl is DatatypeDecl) {
        return string.Format("{0}.Default().({1})", RuntimeTypeDescriptor(type, tok, wr), TypeName(udt, wr, tok));
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
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
    protected static string FormatTraitInterfaceName(string traitName) =>
      string.Format("Iface_{0}_", traitName);

    protected string TypeName_Related(Func<string, string> formatter, Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
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

    protected string TypeName_Constructor(DatatypeCtor ctor, TextWriter wr) {
      var ptr = ctor.EnclosingDatatype is CoDatatypeDecl ? "*" : "";
      return string.Format("{0}{1}_{2}", ptr, TypeName(UserDefinedType.FromTopLevelDecl(ctor.tok, ctor.EnclosingDatatype), wr, ctor.tok), ctor.CompileName);
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member) {
      // XXX This duplicates some of the logic in UserDefinedTypeName, but if we
      // don't do it here, we end up passing the name of the module to
      // FormatCompanionName, which doesn't help anyone
      if (type is UserDefinedType udt && udt.ResolvedClass != null && IsExternMemberOfExternModule(member, udt.ResolvedClass)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!udt.ResolvedClass.Module.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(udt.ResolvedClass.Module.CompileName);
      }
      return TypeName_Related(FormatCompanionName, type, wr, tok, member);
    }

    protected string TypeName_CompanionType(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatCompanionTypeName, type, wr, tok);
    }

    protected string TypeName_Initializer(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatInitializerName, type, wr, tok);
    }

    protected string TypeName_RTD(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatRTDName, type, wr, tok);
    }

    protected string TypeName_TraitInterface(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatTraitInterfaceName, type, wr, tok);
    }

    protected string ClassName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      return type is UserDefinedType udt ? FullTypeName(udt, member) : TypeName(type, wr, tok, member);
    }

    protected string UnqualifiedClassName(Type type, TextWriter wr, Bpl.IToken tok) {
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
      if (type.AsSeqType is SeqType st && st.Arg.IsCharType) {
        return NativeStringType;
      } else {
        return type;
      }
    }

    /// A type which is rendered to Go exactly as specified.  Used to represent the native string type.
    private class SpecialNativeType : UserDefinedType {
      internal SpecialNativeType(string name) : base(Bpl.Token.NoToken, name, null) { }
    }

    private readonly static SpecialNativeType NativeStringType = new SpecialNativeType("string");

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isExtern, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string/*?*/ rhs, string className, TargetWriter wr, TargetWriter initWriter, TargetWriter concreteMethodWriter) {
      if (isExtern) {
        Error(tok, "Unsupported field {0} in extern trait", wr, name);
      }

      if (isConst && rhs != null) {
        var receiver = isStatic ? FormatCompanionTypeName(className) : className;
        var wBody = concreteMethodWriter.NewNamedBlock("func (_this *{0}) {1}() {2}", receiver, name, TypeName(type, concreteMethodWriter, tok));
        wBody.WriteLine("return {0}", rhs);
      } else {
        if (rhs == null) {
          rhs = DefaultValue(type, initWriter, tok);
        }

        wr.WriteLine("{0} {1}", name, TypeName(type, initWriter, tok));

        if (!isStatic) {
          initWriter.WriteLine("_this.{0} = {1}", name, rhs);
        } else {
          initWriter.WriteLine("{0}: {1},", name, rhs);
        }
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      if (isInParam) {
        wr.Write("{0}{1} {2}", prefix, name, TypeName(type, wr, tok));
        return true;
      } else {
        return false;
      }
    }

    private TargetWriter/*?*/ DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool includeRhs, bool leaveRoomForRhs, TargetWriter wr) {
      wr.Write("var {0}", name);

      if (type != null) {
        // Always specify the type in case the rhs is nil
        wr.Write(" {0}", TypeName(type, wr, tok));
      }

      TargetWriter w;
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

        wr.WriteLine("var _ = {0}", name);
      }

      return w;
    }

    protected override void DeclareLocalVar(string name, Type type, Bpl.IToken tok, bool leaveRoomForRhs, string rhs, TargetWriter wr) {
      var w = DeclareLocalVar(name, type, tok, includeRhs:(rhs != null || leaveRoomForRhs), leaveRoomForRhs:leaveRoomForRhs, wr:wr);
      if (rhs != null) {
        w.Write(rhs);
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, TargetWriter wr) {
      return DeclareLocalVar(name, type, tok, includeRhs:true, leaveRoomForRhs:false, wr:wr);
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override bool NeedsCastFromTypeParameter => true;
    protected override bool SupportsMultipleReturns => true;
    protected override string StmtTerminator => "";

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      // emit nothing; this is only for actual parametric polymorphism, not RTDs
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return "var " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitMultiAssignment(out List<TargetWriter> wLhss, List<Type> lhsTypes, out List<TargetWriter> wRhss, List<Type> rhsTypes, TargetWriter wr) {
      Contract.Assert(lhsTypes.Count == rhsTypes.Count);
      wLhss = new List<TargetWriter>();
      wRhss = new List<TargetWriter>();

      var sep = "";
      foreach (var _ in lhsTypes) {
        wr.Write(sep);
        var wLhs = wr.Fork();
        wLhss.Add(wLhs);
        sep = ", ";
      }

      wr.Write(" = ");

      sep = "";
      for (int i = 0; i < rhsTypes.Count; i++) {
        wr.Write(sep);
        var wRhs = wr.Fork();
        wRhs = EmitCoercionIfNecessary(from:rhsTypes[i], to:lhsTypes[i], tok:null, wr:wRhs);
        wRhss.Add(wRhs);
        sep = ", ";
      }

      wr.WriteLine();
    }

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Write("_dafny.Print(");
      TrExpr(arg, wr, false);
      wr.WriteLine(")");
    }

    protected override void EmitReturn(List<Formal> formals, TargetWriter wr) {
      var outParams = formals.Where(f => !f.IsGhost).ToList();
      if (!outParams.Any()) {
        wr.WriteLine("return");
      } else {
        wr.WriteLine("return {0}", Util.Comma(outParams, IdName));
      }
    }

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      var w = wr.ForkSection();
      wr.IndentLess();
      wr.WriteLine("L{0}:", label);
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, TargetWriter wr) {
      if (label == null) {
        wr.WriteLine("break");
      } else {
        wr.WriteLine("goto L{0}", label);
      }
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.WriteLine("_yielded <- struct{}{}");
      wr.WriteLine("_, _ok = <- _cont");
      wr.WriteLine("if !_ok { return }");
    }

    protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("panic(\"{0}\")", message);
    }

    protected override BlockTargetWriter CreateWhileLoop(out TargetWriter guardWriter, TargetWriter wr) {
      wr.Write("for ");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlock("");
      return wBody;
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock("for {0} := _dafny.Zero; {0}.Cmp({1}) < 0; {0} = {0}.Plus(_dafny.One)", indexVar, bound);
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock("for {0} := _dafny.IntOf({1}); ; {0} = {0}.Times(_dafny.Two)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0} = {0}.Plus(_dafny.One)", varName);
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0} = {0}.Minus(_dafny.One)", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return "_dafny.Quantifier";
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type/*?*/ boundVarType, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null) {
      var okVar = FreshId("_ok");
      var iterVar = FreshId("_iter");
      var valVar = boundVarType == null ? boundVar : FreshId("_val");
      wr.Write("for {0} := _dafny.Iterate(", iterVar);
      collectionWriter = wr.Fork();
      var wBody = wr.NewBlock(");;");
      wBody.WriteLine("{0}, {1} := {2}()", valVar, okVar, iterVar);
      wBody.WriteLine("if !{0} {{ break }}", okVar);
      if (boundVarType != null) {
        wBody.WriteLine("{0} := {1}.({2})", boundVar, valVar, TypeName(boundVarType, wBody, tok));
      }

      if (altBoundVarName != null) {
        if (altVarType == null) {
          wBody.WriteLine("{0} = {1}", altBoundVarName, boundVar);
        } else {
          wBody.WriteLine("{0} := {1}", altBoundVarName, boundVar);
        }
      }

      return wBody;
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
      if (cl != null) {
        if (cl.Name == "object") {
          wr.Write("new(struct{})");
        } else {
          wr.Write("{0}(", TypeName_Initializer(type, wr, tok));
          EmitRuntimeTypeDescriptorsActuals(type.TypeArgs, cl.TypeArgs, tok, true, wr);
          wr.Write(")");
        }
      } else {
        wr.Write("new({0})", TypeName(type, wr, tok));
      }
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      var initValue = DefaultValue(elmtType, wr, tok);

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
        TrExpr(dim, wr, false);
        sep = ", ";
      }

      wr.Write(")");
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write("{0}", TypeName_Companion(((UserDefinedType) e.Type).ResolvedClass, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("({0})(nil)", TypeName(e.Type, wr, tok:null));
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("_dafny.Char('{0}')", TranslateEscapes(v, isChar:true));
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("_dafny.SeqOfString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) is NativeType nt) {
        wr.Write("{0}({1})", GetNativeTypeName(nt), (BigInteger)e.Value);
      } else if (e.Value is BigInteger i) {
        EmitIntegerLiteral(i, wr);
      } else if (e.Value is Basetypes.BigDec n) {
        var zeros = Util.Repeat("0", Math.Abs(n.Exponent));
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
    }
    void EmitIntegerLiteral(BigInteger i, TextWriter wr) {
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

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      var n = str.Length;
      if (!isVerbatim) {
        wr.Write("\"{0}\"", TranslateEscapes(str, isChar:false));
      } else {
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i+1 < n && str[i+1] == '\"') {
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

      // Painfully, Go doesn't support octal escapes with fewer than three
      // digits, so we have to expand them.
      s = ShortOctalEscape.Replace(s, match => {
        switch (match.Length) {
          case 2: return "\\00" + match.Groups[1];
          case 3: return "\\0" + match.Groups[1];
          default: throw new Exception("Unexpected match of length " + match.Length);
        }
      });

      // Similarly with hex escapes with only one digit
      s = ShortHexEscape.Replace(s, match => "\\x0" + match.Groups[1]);

      return s;
    }

    private static Regex ShortOctalEscape = new Regex(@"(?<!\\)\\([0-7][0-7]?)(?![0-7])");
    private static Regex ShortHexEscape = new Regex(@"(?<!\\)\\([0-9a-fA-F])(?![0-9a-fA-F])");

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr) {
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

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out _, out _, out needsCast);
      }

      var bv = e0.Type.AsBitVectorType;
      if (bv.Width == 0) {
        tr(e0, wr, inLetExprBody);
      } else {
        TargetWriter wFirstArg;
        if (bv.NativeType != null) {
          wr.Write("_dafny.{0}{1}(", isRotateLeft ? "Lrot" : "Rrot", Capitalize(GetNativeTypeName(bv.NativeType)));
          wFirstArg = wr.Fork();
          wr.Write(", ");
        } else {
          wr.Write('(');
          wFirstArg = wr.Fork();
          wr.Write(").{0}(", isRotateLeft ? "Lrot" : "Rrot");
        }
        TrExpr(e0, wFirstArg, inLetExprBody);
        TrExpr(e1, wr, inLetExprBody);
        wr.Write(", {0})", bv.Width);

        if (needsCast) {
          wr.Write(".Int64()");
        }
      }
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr) {
      wr.Write("_dafny.NewBuilder()");
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      wr.Write("{0}.Add(_dafny.TupleOf(", ingredients);
      var wrTuple = wr.Fork();
      wr.WriteLine("))");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write("(*({0}).IndexInt({1}))", prefix, i);
    }

    protected override string IdName(TopLevelDecl d) {
      return IdName((Declaration) d);
    }

    protected override string IdName(MemberDecl member) {
      return IdName((Declaration) member);
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
    public static string PublicIdProtect(string name) {
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
      return UserDefinedTypeName(udt, full:true, member:member);
    }

    private string UnqualifiedTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      return UserDefinedTypeName(udt, full:false, member:member);
    }

    private string UserDefinedTypeName(UserDefinedType udt, bool full, MemberDecl/*?*/ member = null) {
      Contract.Requires(udt != null);
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      } else {
        return UserDefinedTypeName(cl, full, member);
      }
    }

    private string FullTypeName(TopLevelDecl cl, MemberDecl/*?*/ member = null) {
      return UserDefinedTypeName(cl, true, member:member);
    }

    private string UnqualifiedTypeName(TopLevelDecl cl, MemberDecl/*?*/ member = null) {
      return UserDefinedTypeName(cl, full:false, member:member);
    }

    private string UserDefinedTypeName(TopLevelDecl cl, bool full, MemberDecl/*?*/ member = null) {
      if (IsExternMemberOfExternModule(member, cl)) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.Module.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(cl.Module.CompileName);
      } else {
        if (cl.IsExtern(out var qual, out _)) {
          // No need to take into account the second argument to extern, since
          // it'll already be cl.CompileName
          if (qual == null) {
            qual = cl.Module.CompileName;
          }
          // Don't use IdName since that'll capitalize, which is unhelpful for
          // built-in types
          return qual + (qual == "" ? "" : ".") + cl.CompileName;
        } else if (!full || cl.Module.IsDefaultModule || this.ModuleName == cl.Module.CompileName) {
          return IdName(cl);
        } else {
          return cl.Module.CompileName + "." + IdName(cl);
        }
      }
    }

    private bool IsExternMemberOfExternModule(MemberDecl/*?*/ member, TopLevelDecl cl) {
      return member != null && cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cdecl.Module.Attributes, "extern") && member.IsExtern(out _, out _);
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("_this");
    }

    protected override void EmitNull(Type type, TargetWriter wr) {
      if (type.IsIntegerType || type.IsBitVectorType || type.AsNewtype != null) {
        wr.Write("_dafny.NilInt");
      } else if (type.IsRealType) {
        wr.Write("_dafny.NilReal");
      } else {
        wr.Write("({0})(nil)", TypeName(type, wr, tok:null));
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, bool inLetExprBody, TargetWriter wr) {
      wr.Write("(func () {0} {{ if ", TypeName(thn.Type, wr, null));
      TrExpr(guard, wr, inLetExprBody);
      wr.Write(" { return ");
      TrExpr(thn, wr, inLetExprBody);
      wr.Write(" }; return ");
      TrExpr(els, wr, inLetExprBody);
      wr.Write(" })() ");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, TargetWriter wr) {
      var ctorName = ctor.CompileName;

      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.TupleOf({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate:  Dt{Dt_Ctor{arguments}}
        wr.Write("{0}{{{1}{0}_{2}{{{3}}}}}",
          FullTypeName(dt), dt is IndDatatypeDecl ? "" : "&", ctorName,
          arguments);
      } else {
        // Co-recursive call
        // Generate:  Companion_Dt_.LazyDt(func () Dt => Companion_Dt_.CreateCtor(args))
        var companionName = TypeName_Companion(dt, wr, dt.tok);
        wr.Write("{0}.{1}(func () {2} ", companionName, FormatLazyConstructorName(dt.CompileName), IdName(dt));
        wr.Write("{{ return {0}.{1}({2}) }}", companionName, FormatDatatypeConstructorName(ctorName), arguments);
        wr.Write(')');
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          compiledName = string.Format("Len({0})", idParam == null ? 0 : (int) idParam);
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

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr) {
      TargetWriter wSource;
      if (member is DatatypeDestructor dtor) {
        wr = EmitCoercionIfNecessary(from:dtor.Type, to:expectedType, tok:null, wr:wr);
        if (dtor.EnclosingClass is TupleTypeDecl) {
          wr.Write("(*(");
          wSource = wr.Fork();
          wr.Write(").IndexInt({0}))", dtor.Name);
        } else {
          wSource = wr.Fork();
          wr.Write(".{0}()", FormatDatatypeDestructorName(dtor.CompileName));
        }
      } else if (!isLValue && member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        wr = EmitCoercionIfNecessary(from:sf.Type, to:expectedType, tok:null, wr:wr);
        wSource = wr.Fork();
        string compiledName;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out _, out _);
        if (compiledName.Length != 0) {
          wr.Write(".{0}", Capitalize(compiledName));
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
        }
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        // sf2 is needed here only because the scope rules for these pattern matches are asinine: sf is *still in scope* but it's useless because it may not have been assigned to!

        wr = EmitCoercionIfNecessary(from:sf2.Type, to:expectedType, tok:null, wr:wr);
        wSource = wr.Fork();
        // FIXME This is a pretty awful string hack.
        wr.Write(".{0}()", FormatDatatypeConstructorCheckName(fieldName.Substring(3)));
      } else if (member is ConstantField cf && cf.Rhs != null) {
        wSource = wr.Fork();
        var customReceiver = NeedsCustomReceiver(member);
        wr.Write(".{0}{1}", IdName(member), customReceiver ? "" : "()");
      } else if (member is Field f && !isLValue) {
        wr = EmitCoercionIfNecessary(from:f.Type, to:expectedType, tok:null, wr:wr);
        wSource = wr.Fork();
        wr.Write(".{0}", IdName(member));
      } else {
        wSource = wr.Fork();
        wr.Write(".{0}", IdName(member));
      }
      return wSource;
    }

    // TODO We might be able to be more consistent about whether indices are ints or Ints and avoid this
    private static string IntOfAny(string i) {
      return string.Format("_dafny.IntOfAny({0})", i);
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      wr.Write("*(");
      var w = wr.Fork();
      wr.Write(".Index({0})).({1})", Util.Comma(indices, IntOfAny), TypeName(elmtType, wr, Bpl.Token.NoToken));
      return w;
    }

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      wr.Write("(*");
      var w = wr.Fork();
      wr.Write(".Index(");
      var sep = "";
      foreach (var index in indices) {
        wr.Write(sep);
        // No need for IntOfAny; things coming from user code are presumed Ints
        TrParenExpr(index, wr, inLetExprBody);
        sep = ", ";
      }
      wr.Write(")).({0})", TypeName(elmtType, wr, Bpl.Token.NoToken));
      return w;
    }

    protected override void EmitArraySelectAsLvalue(string array, List<string> indices, Type elmtType, TargetWriter wr) {
      wr.Write("*({0}.Index({1}))", array, Util.Comma(indices, IntOfAny));
    }

    protected override TargetWriter EmitArrayUpdate(List<string> indices, string rhs, Type elmtType, TargetWriter wr) {
      wr.Write("*(");
      var w = wr.Fork();
      wr.Write(".Index({0})) = {1}", Util.Comma(indices, IntOfAny), rhs);
      return w;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr) {
      if (expr is LiteralExpr lit) {
        wr.Write(lit.Value.ToString());
      } else {
        TrParenExpr(expr, wr, inLetExprBody);
        if (AsNativeType(expr.Type) == null) {
          wr.Write(".Int()");
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      var type = source.Type.NormalizeExpand();
      if (type is SeqType seqType) {
        TrParenExpr(source, wr, inLetExprBody);
        wr.Write(".Index(");
        TrExprToBigInt(index, wr, inLetExprBody);
        wr.Write(").({0})", TypeName(seqType.Arg, wr, null));
      } else if (type is MultiSetType) {
        TrParenExpr(source, wr, inLetExprBody);
        wr.Write(".Multiplicity(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(")");
      } else {
        Contract.Assert(type is MapType);
        // map or imap
        TrParenExpr(source, wr, inLetExprBody);
        wr.Write(".Get(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(").({0})", TypeName(((MapType) type).Range, wr, null));
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr, bool nativeIndex = false) {
      EmitIndexCollectionUpdate(out var wSource, out var wIndex, out var wValue, wr);
      TrParenExpr(source, wSource, inLetExprBody);
      TrExpr(index, wIndex, inLetExprBody);
      TrExpr(value, wValue, inLetExprBody);
    }

    protected override void EmitIndexCollectionUpdate(out TargetWriter wSource, out TargetWriter wIndex, out TargetWriter wValue, TargetWriter wr, bool nativeIndex = false) {
      wSource = wr.Fork();
      wr.Write(nativeIndex ? ".UpdateInt(" : ".Update(");
      wIndex = wr.Fork();
      wr.Write(", ");
      wValue = wr.Fork();
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
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

    void TrExprToBigInt(Expression e, TargetWriter wr, bool inLetExprBody) {
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
          case NativeType.Selection.Number:
          case NativeType.Selection.Long:
            wr.Write("_dafny.IntOfInt64(");
            break;
          default:
            throw new cce.UnreachableException();  // unepxected nativeType.Selection value
        }
      }

      TrParenExpr(e, wr, inLetExprBody);

      if (nativeType != null) {
        wr.Write(")");
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr) {
      wr.Write("_dafny.SeqCreate(");
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      var fromType = (UserDefinedType)expr.Initializer.Type.NormalizeExpand();
      var atd = (ArrowTypeDecl)fromType.ResolvedClass;
      var tParam = new UserDefinedType(expr.tok, new TypeParameter(expr.tok, "X", TypeParameter.TPVarianceSyntax.NonVariant_Strict));
      var toType = new ArrowType(expr.tok, atd, new List<Type>() { Type.Int }, tParam);
      var initWr = EmitCoercionIfNecessary(fromType, toType, expr.tok, wr);
      TrExpr(expr.Initializer, initWr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
      var eeType = expr.E.Type.NormalizeExpand();
      if (eeType is SeqType) {
        TrParenExpr("_dafny.MultiSetFromSeq", expr.E, wr, inLetExprBody);
      } else if (eeType is SetType) {
        TrParenExpr("_dafny.MultiSetFromSet", expr.E, wr, inLetExprBody);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(function, wr, inLetExprBody);
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs, List<Type> boundTypes, Type type, Bpl.IToken tok, bool inLetExprBody, TargetWriter wr) {
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
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr) {
      wr.Write("{0}.{1}()", source, FormatDatatypeConstructorCheckName(ctor.CompileName));
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("(*({0}).IndexInt({1})).({2})", source, formalNonGhostIndex, TypeName(typeArgs[formalNonGhostIndex], wr, Bpl.Token.NoToken));
      } else {
        var dtorName = DatatypeFieldName(dtor, formalNonGhostIndex);
        wr = EmitCoercionIfNecessary(from:dtor.Type, to:bvType, tok:dtor.tok, wr:wr);
        wr.Write("{0}.Get().({1}).{2}", source, TypeName_Constructor(ctor, wr), dtorName);
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      wr.Write("func (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1} {2}", i == 0 ? "" : ", ", inNames[i], TypeName(inTypes[i], wr, tok));
      }
      var w = wr.NewExprBlock(") {0}", TypeName(resultType, wr, tok));
      return w;
    }

    private TargetWriter CreateIIFE_ExprBody(out TargetWriter sourceWriter, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewExprBlock("func ({0} {1}) {2}", bvName, TypeName(sourceType, wr, sourceTok), TypeName(resultType, wr, resultTok));
      w.Write("return ");
      var wExpr = w.Fork();
      w.WriteLine();
      wr.Write('(');
      sourceWriter = wr.Fork();
      wr.Write(')');
      return wExpr;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      TargetWriter sourceWriter;
      var w = CreateIIFE_ExprBody(out sourceWriter, sourceType, sourceTok, resultType, resultTok, bvName, wr);
      TrExpr(source, sourceWriter, inLetExprBody);
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      TargetWriter sourceWriter;
      var w = CreateIIFE_ExprBody(out sourceWriter, sourceType, sourceTok, resultType, resultTok, bvName, wr);
      sourceWriter.Write(source);
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      var w = wr.NewBigExprBlock("func () " + TypeName(resultType, wr, resultTok), "()");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewExprBlock("func ({0} int) {1}", bvName, TypeName(resultType, wr, resultTok));
      wr.Write("({0})", source);
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            wr.Write("^ ");
            TrParenExpr(expr, wr, inLetExprBody);
          } else {
            TrParenExpr(expr, wr, inLetExprBody);
            wr.Write(".Not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr(expr, wr, inLetExprBody);
          wr.Write(".Cardinality()");
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    private bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null || (t.NormalizeExpand() is UserDefinedType udt && !t.IsArrowType && udt.ResolvedClass is ClassDecl);
    }

    private bool IsOrderedByCmp(Type t) {
      return t.IsIntegerType || t.IsRealType || (t.IsBitVectorType && t.AsBitVectorType.NativeType == null) || (t.AsNewtype is NewtypeDecl nt && nt.NativeType == null);
    }

    private bool IsComparedByEquals(Type t) {
      return t.IsArrayType || t.IsIndDatatype || t.NormalizeExpand() is CollectionType;
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, Bpl.IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      TextWriter errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "=="; break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!"; opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||"; break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&"; break;
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
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (!EqualsUpToParameters(e0.Type, e1.Type)) {
              staticCallString = "_dafny.AreEqual";
            } else if (IsOrderedByCmp(e0.Type)) {
              callString = "Cmp";
              postOpString = " == 0";
            } else if (IsComparedByEquals(e0.Type)) {
              callString = "Equals";
            }else if (IsDirectlyComparable(e0.Type)) {
              opString = "==";
            } else {
              staticCallString = "_dafny.AreEqual";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
              postOpString = "/* handle */";
            } else if (!EqualsUpToParameters(e0.Type, e1.Type)) {
              preOpString = "!";
              staticCallString = "_dafny.AreEqual";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "!=";
              postOpString = "/* dircomp */";
            } else if (IsOrderedByCmp(e0.Type)) {
              callString = "Cmp";
              postOpString = " != 0";
            } else if (IsComparedByEquals(e0.Type)) {
              preOpString = "!";
              callString = "Equals";
            } else {
              preOpString = "!";
              staticCallString = "_dafny.AreEqual";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " < 0";
          } else {
            opString = "<";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " <= 0";
          } else {
            opString = "<=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          if (IsOrderedByCmp(e0.Type)) {
            callString = "Cmp";
            postOpString = " >= 0";
          } else {
            opString = ">=";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
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
              staticCallString =  "_dafny.Div" + Capitalize(GetNativeTypeName(AsNativeType(resultType)));
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
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          preOpString = "!"; callString = "Equals"; break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "IsProperSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "IsSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          callString = "IsSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          callString = "IsProperSupersetOf"; break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
        case BinaryExpr.ResolvedOpcode.MapDisjoint:
          callString = "IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!"; callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersection"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "Concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "Contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!"; callString = "Contains"; reverseArguments = true; break;

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
      }
    }

    protected override void EmitIsZero(string varName, TargetWriter wr) {
      wr.Write("{0}.Cmp(_dafny.Zero) == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("_dafny.RealOfFrac(");
          TargetWriter w;
          if (AsNativeType(e.E.Type) is NativeType nt) {
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(nt)));
            w = wr.Fork();
            wr.Write(")");
          } else {
            w = wr;
          }
          TrParenExpr(e.E, w, inLetExprBody);
          wr.Write(", _dafny.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write("_dafny.Char(");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int32())");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            wr.Write(GetNativeTypeName(toNative));
            TrParenExpr(e.E, wr, inLetExprBody);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("_dafny.IntOfInt32(rune(");
              TrExpr(e.E, wr, inLetExprBody);
              wr.Write("))");
            } else {
              // char -> native
              wr.Write(GetNativeTypeName(toNative));
              TrParenExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            TrExpr(e.E, wr, inLetExprBody);
          } else if (fromNative != null) {
            Contract.Assert(toNative == null); // follows from other checks

            // native (int or bv) -> big-integer (int or bv)
            wr.Write("_dafny.IntOf{0}(", Capitalize(GetNativeTypeName(fromNative)));
            TrExpr(e.E, wr, inLetExprBody);
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
              TrParenExpr(u.E, wr, inLetExprBody);
              wr.Write(".CardinalityInt())");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              wr.Write("{0}(", GetNativeTypeName(toNative));
              TrParenExpr(m.Obj, wr, inLetExprBody);
              wr.Write(".LenInt(0))");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody);
              wr.Write(".{0}()", Capitalize(GetNativeTypeName(toNative)));
            }

          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int()");
          if (AsNativeType(e.ToType) is NativeType nt) {
            wr.Write(".{0}()", Capitalize(GetNativeTypeName(nt)));
          }
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
        // identity will do
        TrExpr(e.E, wr, inLetExprBody);
      }
    }

    private static bool EqualsUpToParameters(Type type1, Type type2) {
      // TODO Consider whether Type.SameHead should return true in this case
      return Type.SameHead(type1, type2) || type1.IsArrayType && type1.IsArrayType;
    }

    protected override TargetWriter EmitCoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, Bpl.IToken tok, TargetWriter wr) {
      if (to == null) {
        return wr;
      }

      from = from?.NormalizeExpand();
      to = to.NormalizeExpand();
      if (from != null && from.IsArrowType && to.IsArrowType && !from.Equals(to)) {
        // Need to convert functions more often, so do this before the
        // EqualsUpToParameters check below
        ArrowType fat = from.AsArrowType, tat = to.AsArrowType;
        wr.Write("func (");
        var sep = "";
        var args = new List<string>();
        foreach (Type toArgType in tat.Args) {
          var arg = FreshId("arg");
          args.Add(arg);
          wr.Write("{0}{1} {2}", sep, arg, TypeName(toArgType, wr, tok));
          sep = ", ";
        }
        wr.Write(')');
        if (tat.Result != null) {
          wr.Write(" {0}", TypeName(tat.Result, wr, tok));
        }
        var wBody = wr.NewExprBlock("");
        TargetWriter wCall;
        if (fat.Result == null) {
          wCall = wBody;
        } else {
          wBody.Write("return ");
          wCall = EmitCoercionIfNecessary(from:fat.Result, to:tat.Result, tok:tok, wr:wBody);
        }
        wCall.Write('(');
        var ans = wCall.Fork();
        wCall.Write(")(");
        Contract.Assert(fat.Args.Count == tat.Args.Count);
        sep = "";
        for (int i = 0; i < fat.Args.Count; i++) {
          var fromArgType = fat.Args[i];
          var toArgType = tat.Args[i];
          wCall.Write(sep);
          var w = EmitCoercionIfNecessary(from:toArgType, to:fromArgType, tok:tok, wr:wCall);
          w.Write(args[i]);
          sep = ", ";
        }
        wCall.Write(')');
        return ans;
      } else if (to.IsTypeParameter || from != null && EqualsUpToParameters(from, to)) {
        // do nothing
        return wr;
      } else if (from != null && Type.IsSupertype(to, from)) {
        // upcast
        if (to.IsObjectQ) {
          // Cast to interface{} is one of the few upcasts we can actually do
          return wr;
        } else if (to.IsTraitType && ((UserDefinedType) to).ResolvedClass.IsExtern(out _, out _)) {
          // An extern trait is a plain interface; no need to project an embedded thing
          return wr;
        } else {
          var w = wr.Fork();
          wr.Write(".{0}", UnqualifiedClassName(to, wr, tok));
          return w;
        }
      } else if (from == null || from.IsTypeParameter || Type.IsSupertype(from, to)) {
        // downcast (allowed?) or implicit cast from parameter
        var w = wr.Fork();
        if (from is UserDefinedType fromUdt && fromUdt.ResolvedClass != null && fromUdt.ResolvedClass.ViewAsClass is TraitDecl) {
          wr.Write(".{0}", TypeName_TraitInterface(from, wr, tok));
        }
        wr.Write(".({0})", TypeName(to, wr, tok));
        return w;
      } else {
        Error(tok, "Cannot convert from {0} to {1}", wr, from, to);
        return wr;
      }
    }

    protected override TargetWriter EmitCoercionToNativeForm(Type from, Bpl.IToken tok, TargetWriter wr) {
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

    protected override TargetWriter EmitCoercionFromNativeForm(Type to, Bpl.IToken tok, TargetWriter wr) {
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

    protected override TargetWriter EmitCoercionToNativeInt(TargetWriter wr) {
      var w = wr.Fork();
      wr.Write(".(int)");
      return w;
    }

    protected override TargetWriter EmitCoercionToArbitraryTuple(TargetWriter wr) {
      var w = wr.Fork();
      wr.Write(".(_dafny.Tuple)");
      return w;
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("_dafny.SetOf");
      } else if (ct is MultiSetType) {
        wr.Write("_dafny.MultiSetOf");
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        if (ct.Arg.IsCharType) {
          wr.Write("_dafny.SeqOfChars");
        } else {
          wr.Write("_dafny.SeqOf");
        }
      }
      TrExprList(elements, wr, inLetExprBody, type: ct.TypeArgs[0]);
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("_dafny.NewMapBuilder()");
      foreach (ExpressionPair p in elements) {
        wr.Write(".Add(");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(", ");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write(')');
      }
      wr.Write(".ToMap()");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is MapType) {
        wr.Write("_dafny.NewMapBuilder()");
      } else if (ct is SetType || ct is MultiSetType) {
        wr.Write("_dafny.NewBuilder()");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      wr.Write("{0}.Add(", collName);
      TrExpr(elmt, wr, inLetExprBody);
      wr.WriteLine(")");
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr) {
      wr.Write("{0}.Add(", collName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine(")");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      if (ct is SetType) {
        return collName + ".ToSet()";
      } else if (ct is MultiSetType) {
        return collName + ".ToMultiSet()";
      } else {
        Contract.Assert(ct is MapType);
        return collName + ".ToMap()";
      }
    }

    protected override void EmitIntegerRange(Type type, out TargetWriter wLo, out TargetWriter wHi, TargetWriter wr) {
      if (AsNativeType(type) != null) {
        wr.Write("{0}.IntegerRange(", TypeName_Companion(type.AsNewtype, wr, tok:Bpl.Token.NoToken));
      } else {
        wr.Write("_dafny.IntegerRange(");
      }
      wLo = wr.Fork();
      wr.Write(", ");
      wHi = wr.Fork();
      wr.Write(')');
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody);
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool SupportsInMemoryCompilation => false;

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (!DafnyOptions.O.RunAfterCompile || callToMain == null) {
        // compile now
        return SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames, outputWriter, hasMain, run:false);
      } else {
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'go run'
        // will run the program.
        return true;
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      return SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames, outputWriter, hasMain:true, run:true);
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

      string verb;
      if (run) {
        verb = "run";
      } else {
        string output;
        var outputToFile = !DafnyOptions.O.RunAfterCompile;

        if (outputToFile) {
          string extension;
          if (hasMain) {
            switch (Environment.OSVersion.Platform) {
              case PlatformID.Unix:
              case PlatformID.MacOSX:
              case (PlatformID) 128: // early Mono
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
            case (PlatformID) 128: // early Mono
              output = "/dev/null";
              break;
            default:
              output = "NUL";
              break;
          }
        }

        verb = string.Format("build -o \"{0}\"", output);
      }

      var args = string.Format("{0} \"{1}\"", verb, targetFilename);
      var psi = new ProcessStartInfo("go", args) {
        CreateNoWindow = Environment.OSVersion.Platform != PlatformID.Win32NT,
        UseShellExecute = false,
        RedirectStandardInput = false,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };
      psi.EnvironmentVariables["GOPATH"] = GoPath(targetFilename);

      try {
        using (var process = Process.Start(psi)) {
          if (process == null) {
            return false;
          }
          process.WaitForExit();
          return process.ExitCode == 0;
        }
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start go ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
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
      using (var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read))) {
        using (var wr = new StreamWriter(new FileStream(tgtFilename, FileMode.OpenOrCreate, FileAccess.Write))) {
          while (rd.ReadLine() is string line) {
            wr.WriteLine(line);
          }
        }
      }

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
      using (var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read))) {
        while (rd.ReadLine() is string line) {
          var match = PackageLine.Match(line);
          if (match.Success) {
            return match.Groups[1].Value;
          }
        }
        return null;
      }
    }

    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*$");
  }
}
