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
using System.Diagnostics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class GoCompiler : Compiler {
    public GoCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    GoCompiler(GoCompiler parent, string moduleName) : base(parent.Reporter) {
      ModuleName = moduleName;
    }

    public override string TargetLanguage => "Go";

    private readonly TargetWriter ImportWriter = new TargetWriter(4);
    private readonly TargetWriter ImportDummyWriter = new TargetWriter();
    private readonly string ModuleName = "_module";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into Go", program.Name);
      wr.WriteLine("package main");
      wr.WriteLine();
      EmitImports(wr);
      wr.WriteLine();
      var rt = wr.NewFile("dafny/dafny.go");
      ReadRuntimeSystem("DafnyRuntime.go", rt);
    }

    void EmitModuleHeader(string moduleName, TargetWriter wr) {
      wr.WriteLine("// Package {0}", moduleName);
      wr.WriteLine("// Dafny module {0} compiled into Go", moduleName);
      wr.WriteLine();
      wr.WriteLine("package {0}", moduleName);
      wr.WriteLine();
      EmitImports(wr);
      wr.WriteLine();
    }

    void EmitImports(TargetWriter wr) {
      wr.WriteLine("import (");
      wr.WriteLine("    \"dafny\"");
      wr.WriteLine("    \"fmt\"");
      wr.WriteLine("    refl \"reflect\"");
      wr.WriteLine("    \"runtime\"");
      wr.Append(ImportWriter);
      wr.WriteLine(")");
      wr.WriteLine("var _ dafny.Char");
      wr.WriteLine("var _ fmt.Stringer");
      wr.WriteLine("var _ refl.Type");
      wr.WriteLine("var _ runtime.Func");
      wr.Append(ImportDummyWriter);
      wr.WriteLine();
      wr.WriteLine("type Dummy struct{}");
    }

    public override void EmitCallToMain(Method mainMethod, TextWriter wr) {
      // We're not actually in the default module, we're in the special package
      // main, so make a child compiler with the correct value for ModuleName
      // so we can get the right companion name

      var subcomp = new GoCompiler(this, "main");
      var companion = subcomp.TypeName_Companion(mainMethod.EnclosingClass as ClassDecl, wr, mainMethod.tok);

      wr.WriteLine("func main() {");
      wr.WriteLine("  {0}.{1}()", companion, IdName(mainMethod));
      wr.WriteLine("}");
    }
      
    TargetWriter CreateDescribedSection(string desc, TargetWriter wr, params object[] args) {
      var body = wr.NewSection();
      var str = string.Format(desc, args);
      body.WriteLine("// Definition of {0}", str);
      wr.WriteLine("// End of {0}", str);
      return body;
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = (cw as GoCompiler.ClassWriter).ConcreteMethodWriter;
      wr.Indent();
      return wr.NewNamedBlock("func (_this * {0}) Main()", FormatCompanionTypeName((cw as GoCompiler.ClassWriter).ClassName));
    }

    protected override TargetWriter CreateModule(string moduleName, bool isExtern, string/*?*/ libraryName, TargetWriter wr) {
      if (isExtern) {
        ImportWriter.Indent();
        ImportWriter.WriteLine("{0} \"{1}\"", IdProtect(moduleName), libraryName);
        return new TargetWriter(); // ignore contents of extern module
      } else {
        // Go ignores all filenames starting with underscores.  So we're forced
        // to rewrite "__default" to "default__".
        var pkgName = moduleName;
        while (pkgName.StartsWith("_")) {
          pkgName = pkgName.Substring(1) + "_";
        }

        // FIXME: This won't work for nested modules.  Add another variable
        // like ImportWriter?
        var filename = string.Format("{0}/{0}.go", pkgName);
        var w = wr.NewFile(filename);
        // Create a new Compiler so it has its own ImportWriter
        var subcomp = new GoCompiler(this, moduleName);
        subcomp.EmitModuleHeader(moduleName, w);

        EmitImport(moduleName, pkgName);

        return w;
      }
    }

    protected void EmitImport(string id, string pkg) {
      ImportWriter.Indent();
      ImportWriter.WriteLine("{0} \"{1}\"", IdProtect(id), pkg);

      ImportDummyWriter.Indent();
      ImportDummyWriter.WriteLine("var _ {0}.Dummy", IdProtect(id));
    }

    protected override string GetHelperModuleName() => "dafny";

    protected override IClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      wr.Indent();
      var w = CreateDescribedSection("class {0}", wr, name);
      
      var instanceFieldWriter = w.NewBlock(string.Format("type {0} struct", name));

      if (typeParameters != null) {
        WriteRuntimeTypeDescriptorsFields(typeParameters, false, instanceFieldWriter);
      }

      CreateInitializer(name, w, out var instanceFieldInitWriter, out var traitInitWriter);

      if (typeParameters != null) {
        // TODO
        // foreach (var tp in typeParameters) {
        //   if (tp.Characteristics.MustSupportZeroInitialization) {
        //     instanceFieldWriter.Indent();
        //     instanceFieldWriter.WriteLine("this.{0} = {0};", "rtd$_" + tp.CompileName);
        //   }
        // }
      }

      var staticFieldWriter = w.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      var staticFieldInitWriter = w.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));

      var cw = new ClassWriter(this, name, null, w, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);

      if (superClasses != null) {
        foreach (Type typ in superClasses) {
          cw.AddSuperType(typ, tok);
        }
      }
      return cw;
    }

    protected override IClassWriter CreateTrait(string name, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      wr.Indent();
      wr = CreateDescribedSection("trait {0}", wr, name);
      var instanceFieldWriter = wr.NewNamedBlock("type {0} struct", name);
      instanceFieldWriter.Indent();
      instanceFieldWriter.WriteLine(FormatTraitInterfaceName(name));
      wr.Indent();
      var abstractMethodWriter = wr.NewBlock(string.Format("type {0} interface", FormatTraitInterfaceName(name)));
      var concreteMethodWriter = wr.Fork();
      wr.Indent();

      CreateInitializer(name, wr, out var instanceFieldInitWriter, out var traitInitWriter);
      
      var staticFieldWriter = wr.NewNamedBlock("type {0} struct", FormatCompanionTypeName(name));
      wr.Indent();
      var staticFieldInitWriter = wr.NewNamedBlock("var {0} = {1}", FormatCompanionName(name), FormatCompanionTypeName(name));
      wr.Indent();
      
      var cw = new ClassWriter(this, name, abstractMethodWriter, concreteMethodWriter, instanceFieldWriter, instanceFieldInitWriter, traitInitWriter, staticFieldWriter, staticFieldInitWriter);
      if (superClasses != null) {
        foreach (Type typ in superClasses) {
          cw.AddSuperType(typ, tok);
        }
      }
      return cw;
    }

    protected void CreateInitializer(string name, TargetWriter wr, out TargetWriter instanceFieldInitWriter, out TargetWriter traitInitWriter) {
      var w = wr.NewNamedBlock("func {0}() *{1}", FormatInitializerName(name), name);
      w.Indent();
      instanceFieldInitWriter = w.NewNamedBlock("__ans := {0}", name);
      traitInitWriter = w.Fork();
      w.Indent();
      w.WriteLine("return &__ans");
    }

    protected override bool NeedsWrappersForInheritedFields() => false;
    protected override bool SupportsProperties() => false;

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
      //   runtime.SetFinalizer(this_, func(_ MyIteratorExample) {
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
      var cw = CreateClass(IdName(iter), iter.TypeArgs, wr) as GoCompiler.ClassWriter;

      cw.InstanceFieldWriter.Indent();
      cw.InstanceFieldWriter.WriteLine("cont chan<- struct{}");
      cw.InstanceFieldWriter.Indent();
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

      cw.ConcreteMethodWriter.Indent();
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
      wCtor.Indent();
      wCtor.WriteLine("_cont := make(chan struct{})");
      wCtor.Indent();
      wCtor.WriteLine("_yielded := make(chan struct{})");
      wCtor.Indent();
      wCtor.WriteLine("_this.cont = _cont");
      wCtor.Indent();
      wCtor.WriteLine("_this.yielded = _yielded");
      wCtor.WriteLine();
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          wCtor.Indent();
          wCtor.WriteLine("_this.{0} = {1}", Capitalize(IdName(p)), IdName(p));
        }
      }
      wCtor.WriteLine();
      wCtor.Indent();
      wCtor.WriteLine("go _this.run(_cont, _yielded)");
      wCtor.WriteLine();
      wCtor.Indent();
      wCtor.WriteLine("runtime.SetFinalizer(_this, func(_ * {0}) {{ close(_cont) }})", IdName(iter));
      
      cw.ConcreteMethodWriter.Indent();
      var wMoveNext = cw.ConcreteMethodWriter.NewNamedBlock("func (_this * {0}) MoveNext() bool", IdName(iter));
      wMoveNext.Indent();
      wMoveNext.WriteLine("_this.cont <- struct{}{}");
      wMoveNext.Indent();
      wMoveNext.WriteLine("_, ok := <- _this.yielded");
      wMoveNext.WriteLine();
      wMoveNext.Indent();
      wMoveNext.WriteLine("return ok");

      var wRun = cw.ConcreteMethodWriter.NewNamedBlock("func (_this * {0}) run(_cont <-chan struct{{}}, _yielded chan<- struct{{}})", IdName(iter));
      wRun.Indent();
      wRun.WriteLine("defer close(_yielded)");
      wRun.WriteLine();
      wRun.Indent();
      wRun.WriteLine("_, _ok := <- _cont");
      wRun.Indent();
      wRun.WriteLine("if !_ok { return }");
      wRun.WriteLine();
      
      return wRun;
    }

    protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
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
      // type companionStruct_Dt_ struct {}
      //
      // var Companion_Dt_ = companionStruct_Dt_ {}
      //
      // ...
      //
      // type Dt_Ctor0 struct {
      //   Field0 type0
      //   Field1 type1
      //   ...
      // }
      // 
      // func (_this Dt_Ctor0) isDt() {}
      //
      // func (_ companionStruct_Dt_) CreateCtor0(field0 type0, field1 type1) Dt {
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
      // func (_this Dt) Dafny_EqualsGeneric_(other interface{}) bool { ... }
      // 
      // TODO AllSingletonConstructors
      // TODO Run-time type descriptors
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
      //   value Dface_Dt_
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
      // func (_ companionStruct_Dt_) LazyDt(f func() Dt) Dt {
      //   return Dt{*lazyDt{nil, f}}
      // }
      //
      // func (_ companionStruct_Dt_) CreateCtor0(field0 type0, field1 type1) Dt {
      //   return Dt{*Dt_Ctor0{type0, type1}}
      // }
      //
      // func (_this * Dt_Ctor0) Get() Dt {
      //   return _this
      // }
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.go
        return;
      }

      string name = IdProtect(dt.CompileName);
      string companionTypeName = FormatCompanionTypeName(name);
      string dataName = FormatDatatypeInterfaceName(name);
      string ifaceName = FormatLazyInterfaceName(name);

      string getData = dt is CoDatatypeDecl ? ifaceName + ".Get()" : dataName;

      Func<DatatypeCtor, string> structOfCtor = ctor =>
        string.Format("{0}{1}_{2}", dt is CoDatatypeDecl ? "*" : "", name, ctor.CompileName);

      wr.Indent();
      // from here on, write everything into the new block created here:
      wr = CreateDescribedSection("{0} {1}", wr, dt is IndDatatypeDecl ? "data type" : "co-data type", name);

      if (dt is IndDatatypeDecl) { 
        wr.Indent();
        var wStruct = wr.NewNamedBlock("type {0} struct", name);
        wStruct.Indent();
        wStruct.WriteLine(dataName);
      } else {
        wr.Indent();
        var wDt = wr.NewNamedBlock("type {0} struct", name);
        wDt.Indent();
        wDt.WriteLine(ifaceName);

        wr.Indent();
        var wIface = wr.NewNamedBlock("type {0} interface", ifaceName);
        wIface.Indent();
        wIface.WriteLine("Get() {0}", dataName);

        wr.Indent();
        var wLazy = wr.NewNamedBlock("type lazy{0} struct", name);
        wLazy.Indent();
        wLazy.WriteLine("value {0}", dataName);
        wLazy.Indent();
        wLazy.WriteLine("init func() {0}", name);

        wr.Indent();
        var wLazyGet = wr.NewNamedBlock("func (_this *lazy{0}) Get() {1}", name, dataName);
        wLazyGet.Indent();
        var wIf = wLazyGet.NewBlock("if _this.value == nil");
        wIf.Indent();
        wIf.WriteLine("_this.value = _this.init().Get()");
        wIf.Indent();
        wIf.WriteLine("_this.init = nil"); // allow GC of values in closure

        wLazyGet.Indent();
        wLazyGet.WriteLine("return _this.value");

        wr.Indent();
        var wLazyCreate = wr.NewNamedBlock("func (_this {0}) {1}(f func () {2}) {2}", companionTypeName, FormatLazyConstructorName(name), name, name);
        wLazyCreate.Indent();
        wLazyCreate.WriteLine("return {0}{{&lazy{0}{{nil, f}}}}", name);
      }

      {
        wr.Indent();
        var wIface = wr.NewNamedBlock("type {0} interface", dataName);
        wIface.Indent();
        wIface.WriteLine("is{0}()", name);
      }

      wr.Indent();
      wr.WriteLine("type {0} struct {{}}", companionTypeName);
      wr.Indent();
      wr.WriteLine("var {0} = {1}{{}}", FormatCompanionName(name), companionTypeName);

      foreach (var ctor in dt.Ctors) {
        var ctorStructName = name + "_" + ctor.CompileName;
        wr.Indent();
        var wStruct = wr.NewNamedBlock("type {0} struct", ctorStructName);
        var k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            wStruct.Indent();
            wStruct.WriteLine("{0} {1}", FormalName(formal, k), TypeName(formal.Type, wr, formal.Tok));
            k++;
          }
        }

        wr.WriteLine();
        wr.Indent();
        wr.WriteLine("func (_this {0}{1}) is{2}() {{}}", dt is CoDatatypeDecl ? "*" : "", ctorStructName, name);
        wr.WriteLine();

        wr.Indent();
        wr.Write("func (_ {0}) {1}(", companionTypeName, FormatDatatypeConstructorName(ctor.CompileName));
        var argNames = new List<string>();
        k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            var formalName = FormalName(formal, k);

            wr.Write("{0}{1} {2}", k > 0 ? ", " : "", formalName, TypeName(formal.Type, wr, formal.Tok));

            argNames.Add(formalName);
            k++;
          }
        }
        var wCreateBody = wr.NewNamedBlock(") {0}", name);
        wCreateBody.Indent();
        wCreateBody.WriteLine("return {0}{{{1}{2}{{{3}}}}}", name, dt is CoDatatypeDecl ? "&" : "", ctorStructName, Util.Comma(argNames));

        wr.Indent();
        var wCheck = wr.NewNamedBlock("func (_this {0}) {1}() bool", name, FormatDatatypeConstructorCheckName(ctor.CompileName));
        wCheck.Indent();
        wCheck.WriteLine("_, ok := _this.{0}.({1})", getData, structOfCtor(ctor));
        wCheck.Indent();
        wCheck.WriteLine("return ok");

        if (dt is CoDatatypeDecl) {
          wr.Indent();
          var wGet = wr.NewNamedBlock("func (_this *{0}) Get() {1}", ctorStructName, dataName);
          wGet.Indent();
          wGet.WriteLine("return _this");
        }
      }

      if (dt.HasFinitePossibleValues) {
        // TODO
      }
      
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              wr.Indent();
              var wDtor = wr.NewNamedBlock("func (_this {0}) {1}() {2}", name, FormatDatatypeDestructorName(arg.CompileName), TypeName(arg.Type, wr, arg.tok));
              wDtor.Indent();
              var n = dtor.EnclosingCtors.Count;
              if (n == 1) {
                wDtor.WriteLine("return _this.{0}.({1}).{2}", getData, structOfCtor(dtor.EnclosingCtors[0]), arg.CompileName);
              } else {
                wDtor = wDtor.NewNamedBlock("switch data := _this.{0}.(type)", getData);
                for (int i = 0; i < n-1; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  wDtor.Indent();
                  wDtor.WriteLine("case {0}: return data.{1}", structOfCtor(ctor_i), IdName(arg));
                }
                Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n-1].CompileName);
                wDtor.Indent();
                wDtor.WriteLine("default: return data.({0}).{1}", structOfCtor(dtor.EnclosingCtors[n-1]), IdName(arg));
              }
            }
          }
        }
      }

      {
        // String() method
        wr.Indent();
        var w = wr.NewNamedBlock("func (_this {0}) String() string", name);
        w.Indent();
        // TODO Avoid switch if only one branch
        w = w.NewNamedBlock("switch {0}_this.{1}.(type)", dt is CoDatatypeDecl ? "" : "data := ", getData);
        foreach (var ctor in dt.Ctors) {
          w.Indent();
          var wCase = w.NewNamedBlock("case {0}:", structOfCtor(ctor));
          wCase.Indent();
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
                wCase.Write("{0}fmt.Sprint(data.{1})", sep, FormalName(arg, k));
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
        w.Indent();
        var wDefault = w.NewBlock("default:");
        wDefault.Indent();
        if (dt is CoDatatypeDecl) {
          wDefault.WriteLine("return \"{0}.{1}.unexpected\"", dt.Module.CompileName, dt.CompileName);
        } else {
          wDefault.WriteLine("var _ = data");
          wDefault.Indent();
          wDefault.WriteLine("return \"<unexpected>\"");
        }
      }

      // Equals method
      {
        wr.Indent();
        var wEquals = wr.NewNamedBlock("func (_this {0}) Equals(other {0}) bool", name);
        // TODO: Way to implement shortcut check for address equality?
        wEquals.Indent();
        wEquals = wEquals.NewNamedBlock("switch data1 := _this.{0}.(type)", getData);
        foreach (var ctor in dt.Ctors) {
          wEquals.Indent();
          var wCase = wEquals.NewNamedBlock("case {0}:", structOfCtor(ctor));
          wCase.Indent();
          wCase.WriteLine("data2, ok := other.{0}.({1})", getData, structOfCtor(ctor));
          wCase.Indent();
          wCase.WriteLine("var _ = data2");
          wCase.Indent();
          wCase.WriteLine("if !ok { return false }");
          var k = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              wCase.Indent();
              wCase.Write("if !(");
              string nm = FormalName(arg, k);
              if (IsDirectlyComparable(arg.Type)) {
                wCase.Write("data1.{0} == data2.{0}", nm);
              } else {
                wCase.Write("dafny.AreEqual(data1.{0}, data2.{0})", nm);
              }
              wCase.WriteLine(") { return false }");
              k++;
            }
          }
          wCase.Indent();
          wCase.WriteLine("return true");
        }
        wEquals.Indent();
        var wDefault = wEquals.NewNamedBlock("default:");
        wDefault.Indent();
        wDefault.WriteLine("var _ = data1");
        wDefault.Indent();
        wDefault.WriteLine("return false; // unexpected");

        wr.Indent();
        var wEqualsGeneric = wr.NewNamedBlock("func (_this {0}) Dafny_EqualsGeneric_(other interface{{}}) bool", name);
        wEqualsGeneric.Indent();
        wEqualsGeneric.WriteLine("typed, ok := other.({0})", name);
        wEqualsGeneric.Indent();
        wEqualsGeneric.WriteLine("return ok && _this.Equals(typed)");
      }
      // TODO: RTD
    }

    protected override void DeclareNewtype(NewtypeDecl nt, TargetWriter wr) {
      var cw = CreateClass(IdName(nt), null, wr) as GoCompiler.ClassWriter;
      var w = cw.ConcreteMethodWriter;
      if (nt.NativeType != null) {
        w.Indent();
        var wIntegerRangeBody = w.NewNamedBlock("func (_this * {0}) IntegerRange(lo dafny.Int, hi dafny.Int) func() (next {1}, ok bool)", FormatCompanionTypeName(IdName(nt)), GetNativeTypeName(nt.NativeType));
        wIntegerRangeBody.Indent();
        wIntegerRangeBody.WriteLine("i, n := lo.Int64(), hi.Int64()");
        wIntegerRangeBody.Indent();
        var wIterFuncBody = wIntegerRangeBody.NewNamedBlock("return func() ({0}, bool)", GetNativeTypeName(nt.NativeType));
        wIterFuncBody.Indent();
        wIterFuncBody.WriteLine("if i >= n { return 0, false }");
        wIterFuncBody.Indent();
        wIterFuncBody.WriteLine("ans := i");
        wIterFuncBody.Indent();
        wIterFuncBody.WriteLine("i++");
        wIterFuncBody.Indent();
        wIterFuncBody.WriteLine("return ans, true");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) { 
        var witness = new TargetWriter(w.IndentLevel);
        if (nt.NativeType == null) {
          TrExpr(nt.Witness, witness, false);
        } else {
          TrParenExpr(nt.Witness, witness, false);
          witness.Write(".toNumber()");
        }
        DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString(), w, null);
      }
      w.Indent();
      var defaultType = nt.NativeType == null ? IdName(nt) : GetNativeTypeName(nt.NativeType);
      using (var wDefault = w.NewNamedBlock("func {0}() {1}", FormatDefaultName(IdProtect(nt.Name)), defaultType)) {
        var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
        var d = TypeInitializationValue(udt, wr, nt.tok, false);
        wDefault.Indent();
        wDefault.WriteLine("return {0};", d);
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr) {
      var cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as GoCompiler.ClassWriter;
      var w = cw.ConcreteMethodWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) { 
        var witness = new TargetWriter(w.IndentLevel);
        TrExpr(sst.Witness, witness, false);
        DeclareField("Witness", true, true, sst.Rhs, sst.tok, witness.ToString(), cw.StaticFieldWriter, cw.StaticFieldInitWriter);
      }
      w.Indent();
      using (var wDefault = w.NewBlock(String.Format("func {0}() {1}", FormatDefaultName(IdProtect(sst.Name)), TypeName(sst.Rhs, w, sst.tok)))) {
        var udt = new UserDefinedType(sst.tok, sst.Name, sst, sst.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp)));
        var d = TypeInitializationValue(udt, wr, sst.tok, false);
        wDefault.Indent();
        wDefault.WriteLine("return {0}", d);
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
      public readonly TargetWriter/*?*/ AbstractMethodWriter, ConcreteMethodWriter, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter;

      public ClassWriter(GoCompiler compiler, string className, TargetWriter abstractMethodWriter, TargetWriter concreteMethodWriter, TargetWriter instanceFieldWriter, TargetWriter instanceFieldInitWriter, TargetWriter traitInitWriter, TargetWriter staticFieldWriter, TargetWriter staticFieldInitWriter) {
        this.Compiler = compiler;
        this.ClassName = className;
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
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, ClassName, AbstractMethodWriter, ConcreteMethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, member, ClassName, ConcreteMethodWriter);
      }
      public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, member, name, out setterWriter, ConcreteMethodWriter);
      }
      public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, FieldWriter(isStatic), FieldInitWriter(isStatic));
      }
      public TextWriter/*?*/ ErrorWriter() => ConcreteMethodWriter;

      public void AddSuperType(Type superType, Bpl.IToken tok) {
        Compiler.AddSuperType(superType, tok, InstanceFieldWriter, InstanceFieldInitWriter, TraitInitWriter, StaticFieldWriter, StaticFieldInitWriter);
      }
    }

    protected BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, string ownerName, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      return CreateSubroutine(IdName(m), m.TypeArgs, m.Ins, m.Outs, null, m.tok, m.IsStatic, m.IsTailRecursive, createBody, ownerName, abstractWriter, concreteWriter);
    }

    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, string ownerName, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      return CreateSubroutine(name, typeArgs, formals, new List<Formal>(), resultType, tok, isStatic, false, createBody, ownerName, abstractWriter, concreteWriter);
    }

    private BlockTargetWriter CreateSubroutine(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> inParams, List<Formal> outParams, Type/*?*/ resultType, Bpl.IToken tok, bool isStatic, bool isTailRecursive, bool createBody, string ownerName, TargetWriter abstractWriter, TargetWriter concreteWriter) {
      TargetWriter wr;
      if (createBody || abstractWriter == null) {
        wr = concreteWriter;
        string receiver = isStatic ? FormatCompanionTypeName(ownerName) : ownerName;
        wr.Indent();
        wr.Write("func (_this * {0}) ", receiver);
      } else {
        wr = abstractWriter;
        wr.Indent();
      }
      wr.Write("{0}(", name);
      var nTypes = WriteRuntimeTypeDescriptorsFormals(typeArgs, false, wr);
      int nIns = WriteFormals(nTypes == 0 ? "" : ", ", inParams, wr);
      wr.Write(")");

      // TODO: Maybe consider using named result parameters, since they're
      // actually close to how Dafny method outs work
      WriteOutTypes(outParams, resultType, wr, tok);

      if (createBody) {
        var w = wr.NewBlock("");

        if (isTailRecursive) {
          w.Indent();
          w.WriteLine("goto TAIL_CALL_START");
          w.Indent();
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

    List<TypeParameter> UsedTypeParameters(DatatypeDecl dt) {
      Contract.Requires(dt != null);

      var idt = dt as IndDatatypeDecl;
      if (idt == null) {
        return dt.TypeArgs;
      } else {
        Contract.Assert(idt.TypeArgs.Count == idt.TypeParametersUsedInConstructionByDefaultCtor.Length);
        var tps = new List<TypeParameter>();
        for (int i = 0; i < idt.TypeArgs.Count; i++) {
          if (idt.TypeParametersUsedInConstructionByDefaultCtor[i]) {
            tps.Add(idt.TypeArgs[i]);
          }
        }
        return tps;
      }
    }

    List<Type> UsedTypeParameters(DatatypeDecl dt, List<Type> typeArgs) {
      Contract.Requires(dt != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(dt.TypeArgs.Count == typeArgs.Count);

      var idt = dt as IndDatatypeDecl;
      if (idt == null) {
        return typeArgs;
      } else {
        Contract.Assert(typeArgs.Count == idt.TypeParametersUsedInConstructionByDefaultCtor.Length);
        var ts = new List<Type>();
        for (int i = 0; i < typeArgs.Count; i++) {
          if (idt.TypeParametersUsedInConstructionByDefaultCtor[i]) {
            ts.Add(typeArgs[i]);
          }
        }
        return ts;
      }
    }

    int WriteRuntimeTypeDescriptorsFields(List<TypeParameter> typeParams, bool useAllTypeArgs, BlockTargetWriter wr) {
      // TODO
      return 0;
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write("{0}{1}", prefix, "ty_" + tp.CompileName);
          prefix = ", ";
          c++;
        }
      }
      return c;
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

    string RuntimeTypeDescriptor(Type type, Bpl.IToken tok, TextWriter wr) {
      // TODO
      return "nil";
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
      instanceFieldWriter.Indent();
      instanceFieldWriter.WriteLine("{0}", TypeName(superType, instanceFieldWriter, tok));

      instanceFieldInitWriter.Indent();
      instanceFieldInitWriter.WriteLine("{0}: {1}(),", ClassName(superType, instanceFieldInitWriter, tok), TypeName_Initializer(superType, instanceFieldInitWriter, tok));

      if (superType is UserDefinedType udt && udt.ResolvedClass.ViewAsClass is TraitDecl) {
        traitInitWriter.Indent();
        traitInitWriter.WriteLine("__ans.{0}.{1} = &__ans", IdProtect(udt.CompileName), FormatTraitInterfaceName(IdProtect(udt.CompileName)));
      }

      staticFieldWriter.Indent();
      staticFieldWriter.WriteLine("* {0}", TypeName_CompanionType(superType, staticFieldWriter, tok));

      staticFieldInitWriter.Indent();
      staticFieldInitWriter.WriteLine("{0}: &{1},", TypeName_CompanionType(superType, staticFieldInitWriter, tok), TypeName_Companion(superType, staticFieldInitWriter, tok, null));
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("goto TAIL_CALL_START");
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "interface {}";
      }

      if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "dafny.Char";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "dafny.Int";
      } else if (xType is RealType) {
        return "dafny.Real";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "dafny.BV";
      } else if (xType.AsNewtype != null) {
        NativeType nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(xType.AsNewtype.BaseType, wr, tok);
      } else if (xType.IsObjectQ) {
        return "interface{}";
      } else if (xType.IsArrayType) {
        return "dafny.Array";
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
          return "dafny.Tuple";
        } else if (udt.IsTypeParameter) {
          return "interface{}";
        }
        if (udt.IsDatatype || udt.IsCoDatatype) {
          // Don't return a pointer to the datatype because the datatype is
          // already represented using a pointer
          return IdProtect(s); 
        } else {
          return TypeName_UDT(s, udt.TypeArgs, wr, udt.tok);
        }
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "dafny.Set";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "dafny.Seq";
      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "dafny.MultiSet";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "dafny.Map";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok, bool inAutoInitContext) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "dafny.Char('D')";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "dafny.Zero";
      } else if (xType is RealType) {
        return "dafny.ZeroReal";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "dafny.Zero";
      } else if (xType is SetType) {
        return "dafny.EmptySet";
      } else if (xType is MultiSetType) {
        return "dafny.EmptyMultiSet";
      } else if (xType is SeqType) {
        return "dafny.EmptySeq";
      } else if (xType is MapType) {
        return "dafny.EmptyMap";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        return "nil";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_Companion(type, wr, tok, null) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return "null";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("func () {0} {{ return {1}; }}", TypeName(udt.TypeArgs.Last(), wr, tok), rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            // non-null array type; we know how to initialize them
            return string.Format("dafny.NewArray({0}, {1})", TypeName_ReflectionType(xType.TypeArgs[0], wr, tok), Util.Comma(arrayClass.Dims, d => string.Format("dafny.IntOf({0})", d)));
          } else {
            return "nil";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return "nil";
        }
      } else if (cl is DatatypeDecl) {
        // TODO: For real, with RTDs
        return "nil";

        // var dt = (DatatypeDecl)cl;
        // var s = dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt);
        // var w = new TargetWriter();
        // w.Write("{0}.Rtd(", s);
        // EmitRuntimeTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), dt.TypeArgs, udt.tok, true, w);
        // w.Write(").Default");
        // return w.ToString();
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(typeArgs != null);
      string s = "*" + IdProtect(fullCompileName);
      return s;
    }

    protected string TypeName_ReflectionType(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok) {
      type = type.NormalizeExpand();
      
      if (type is BoolType) {
        return "dafny.BoolType";
      } else if (type is CharType) {
        return "dafny.CharType";
      } else if (type is IntType || type is BigOrdinalType || type is BitvectorType) {
        return "dafny.IntType";
      } else if (type is RealType) {
        return "dafny.ZeroReal";
      } else if (type is SetType) {
        return "_dafny.Set.Empty";
      } else if (type is MultiSetType) {
        return "_dafny.MultiSet.Empty";
      } else if (type is SeqType) {
        return "_dafny.Seq.of()";
      } else if (type is MapType) {
        return "_dafny.Map.Empty";
      }

      var udt = (UserDefinedType)type;
      if (udt.ResolvedParam != null) {
        return "dafny.TopType";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return string.Format("refl.TypeOf({0}.Witness)", TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok));
        } else if (td.NativeType != null) {
          return string.Format("refl.TypeOf({0}(0))", TypeName(type, wr, tok));
        } else {
          return string.Format("refl.TypeOf({0})", TypeInitializationValue(td.BaseType, wr, tok, false));
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return string.Format("refl.TypeOf({0}.Witness)", TypeName_Companion(type, wr, tok, null));
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name)) {
            var ins = udt.TypeArgs.GetRange(0, udt.TypeArgs.Count - 1);
            var outt = udt.TypeArgs.Last();
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("refl.FuncOf([]refl.Type{{{0}}}, []refl.Type{{{{1}}}}, false)",
              Util.Comma(ins, ty => TypeName_ReflectionType(ty, wr, tok)),
              TypeName_ReflectionType(outt, wr, tok));
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            return "dafny.ArrayType";
          } else {
            return "nil";
          }
        } else {
          return string.Format("refl.TypeOf({0})", TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, false));
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "dafny.IntType";
        } else {
          return string.Format("refl.TypeOf(*{0}{})", IdName(cl));
        }
      } else if (cl is DatatypeDecl) {
        Error(tok, "Type of datatype not implemented", wr);
        return "nil";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected static string FormatCompanionName(string clsName) =>
      string.Format("Companion_{0}_", clsName);
    protected static string FormatCompanionTypeName(string clsName) =>
      // Note that the initial lowercase means the name isn't exported, but it doesn't need to be
      string.Format("companionStruct_{0}_", clsName);
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
    protected static string FormatTraitInterfaceName(string traitName) =>
      string.Format("Iface_{0}_", traitName);

    protected string TypeName_Related(Func<string, string> formatter, Type type, TextWriter wr, Bpl.IToken tok) {
      Contract.Requires(formatter != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      // FIXME This is a hacky bit of string munging.

      string name = ClassName(type, wr, tok);
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

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member) {
      return TypeName_Related(FormatCompanionName, type, wr, tok);
    }

    protected string TypeName_CompanionType(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatCompanionTypeName, type, wr, tok);
    }

    protected string TypeName_Initializer(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatInitializerName, type, wr, tok);
    }

    protected string TypeName_TraitInterface(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName_Related(FormatTraitInterfaceName, type, wr, tok);
    }

    protected string ClassName(Type type, TextWriter wr, Bpl.IToken tok) {
      return type is UserDefinedType udt ? FullTypeName(udt) : TypeName(type, wr, tok);
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr, TargetWriter initWriter) {
      wr.Indent();
      wr.WriteLine("{0} {1}", name, TypeName(type, initWriter, tok));

      initWriter.Indent();
      initWriter.WriteLine("{0} : {1},", name, rhs);
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
      wr.Indent();
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

        wr.Indent();
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

    protected override bool SupportsMultipleReturns() => true;

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("var {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.Indent();
          wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return "var " + target;
    }

    protected override void EmitAssignment(string lhs, Type lhsType, string rhs, Type rhsType, TargetWriter wr) {
      wr.Indent();
      wr.Write("{0} = ", lhs);
      TargetWriter w;
      if (lhsType != null && rhsType != null) {
        w = EmitCoercionIfNecessary(from:rhsType, to:lhsType, tok:Bpl.Token.NoToken, wr:wr);
      } else {
        w = wr;
      }
      w.Write(rhs);
      wr.WriteLine();
    }
    protected override void EmitAssignmentRhs(string rhs, TargetWriter wr) {
      wr.WriteLine(" = {0}", rhs);
    }
    protected override void EmitAssignmentRhs(Expression rhs, bool inLetExprBody, TargetWriter wr) {
      wr.Write(" = ");
      TrExpr(rhs, wr, inLetExprBody);
      wr.WriteLine();
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("fmt.Print(");
      TrExpr(arg, wr, false);
      wr.WriteLine(")");
    }

    protected override void EmitReturn(List<Formal> formals, TargetWriter wr) {
      var outParams = formals.Where(f => !f.IsGhost);
      wr.Indent();
      if (!outParams.Any()) {
        wr.WriteLine("return");
      } else {
        wr.WriteLine("return {0}", Util.Comma(outParams, IdName));
      }
    }

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      wr.Write("L{0}:", label);
      return wr;
    }

    protected override void EmitBreak(string/*?*/ label, TargetWriter wr) {
      wr.Indent();
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("break L{0};", label);
      }
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("_yielded <- struct{}{}");
      wr.Indent();
      wr.WriteLine("_, _ok = <- _cont");
      wr.Indent();
      wr.WriteLine("if !_ok { return }");
    }

    protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.Indent();
      wr.WriteLine("panic(\"{0}\")", message);
    }

    protected override BlockTargetWriter CreateWhileLoop(out TargetWriter guardWriter, TargetWriter wr) {
      wr.Indent();
      wr.Write("for ");
      guardWriter = new TargetWriter(wr.IndentLevel);
      wr.Append(guardWriter);
      var wBody = wr.NewBlock("");
      return wBody;
    }
    
    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      wr.Indent();
      return wr.NewNamedBlock("for {0} := dafny.Zero; {0}.Cmp({1}) < 0; {0} = {0}.Plus(dafny.One)", indexVar, bound);
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      wr.Indent();
      return wr.NewNamedBlock("for {0} := dafny.IntOf({1}); ; {0} = {0}.Times(dafny.Two)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("{0} = {0}.Plus(dafny.One)", varName);
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("{0} = {0}.Minus(dafny.One)", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return string.Format("dafny.Quantifier");
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null) {
      var okVar = FreshId("_ok");
      var iterVar = FreshId("_iter");
      wr.Indent();
      wr.Write("for {0} := dafny.Iterate(", iterVar);
      collectionWriter = wr.Fork();
      var wBody = wr.NewBlock(");;");
      wBody.Indent();
      wBody.WriteLine("{0}, {1} := {2}()", boundVar, okVar, iterVar);
      wBody.Indent();
      wBody.WriteLine("if !{0} {{ break }}", okVar);
      
      if (altBoundVarName != null) {
        wBody.Indent();
        if (altVarType == null) {
          wBody.WriteLine("{0} = {1}", altBoundVarName, boundVar);
        } else {
          wBody.WriteLine("{0} := {1}.({2})", altBoundVarName, boundVar, TypeName(altVarType, wBody, tok));
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
          wr.Write("{0}()", TypeName_Initializer(type, wr, tok));
          // TODO
          //EmitRuntimeTypeDescriptorsActuals(type.TypeArgs, cl.TypeArgs, tok, false, wr);
          //wr.Write(")");
        }
      } else {
        wr.Write("new({0})", TypeName(type, wr, tok));
        // TODO
        //EmitRuntimeTypeDescriptorsActuals(type.TypeArgs, cl.TypeArgs, tok, false, wr);
        //wr.Write(")");
      }
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      var initValue = DefaultValue(elmtType, wr, tok);
      
      string elmtTypeName = TypeName(elmtType, wr, tok);
      
      if (!mustInitialize) {
        wr.Write("dafny.NewArray(refl.TypeOf({0})", initValue);
      } else {
        wr.Write("dafny.NewArrayWithValue({0}", initValue);
      }

      foreach (Expression dim in dimensions) {
        wr.Write(", ");
        TrExpr(dim, wr, false);
      }

      wr.Write(")");
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write("{0}", TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("nil");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("dafny.Char('{0}')", v);
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("dafny.SeqOfString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) != null) {
        wr.Write((BigInteger)e.Value);
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
        wr.Write("dafny.RealOfString(\"{0}\")", str);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
    void EmitIntegerLiteral(BigInteger i, TextWriter wr) {
      Contract.Requires(wr != null);
      if (i == 0) {
        wr.Write("dafny.Zero");
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write("dafny.IntOf({0})", i);
      } else {
        wr.Write("dafny.IntOfString(\"{0}\")", i);
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      var n = str.Length;
      if (!isVerbatim) {
        wr.Write("\"{0}\"", str);
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

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      if (bvType.NativeType == null) {
        wr.Write('(');
        var middle = wr.Fork();
        wr.Write(").Modulo(dafny.One.Lsh(dafny.IntOf({0})))", bvType.Width);
        return middle;
      } else if (bvType.NativeType.Bitwidth == bvType.Width) {
        // no truncation needed
        return wr;
      } else {
        wr.Write("((");
        var middle = new TargetWriter(wr.IndentLevel);
        wr.Append(middle);
        // print in hex, because that looks nice
        wr.Write(") & 0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix);
        return middle;
      }
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      var bv = e0.Type.AsBitVectorType;
      if (bv.Width == 0) {
        tr(e0, wr, inLetExprBody);
      } else {
        TargetWriter wFirstArg;
        if (bv.NativeType != null) {
          wr.Write("dafny.{0}_{1}(", isRotateLeft ? "Lrot" : "Rrot", GetNativeTypeName(bv.NativeType));
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
      wr.Write("[]", tupleTypeArgs);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      wr.Indent();
      wr.Write("{0}.Add(dafny.TupleOf(", ingredients, tupleTypeArgs);
      var wrTuple = wr.Fork();
      wr.WriteLine("))");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write("{0}.Index(dafny.IntOf({1})).Interface()", prefix, i);
    }

    static string Capitalize(string str) {
      Contract.Requires(str != "");
      Contract.Requires(str.Any(c => c != '_'));
      while (str.StartsWith("_")) {
        str = str.Substring(1) + "_";
      }
      if (!char.IsLetter(str[0])) {
        return "Go_" + str;
      } else {
        return char.ToUpper(str[0]) + str.Substring(1);
      }
    }

    protected override string IdName(TopLevelDecl d) {
      Contract.Requires(d != null);
      return Capitalize(d.CompileName);
    }

    protected override string IdName(MemberDecl member) {
      Contract.Requires(member != null);
      return Capitalize(member.CompileName);
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
      Contract.Requires(udt != null);
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      } else if (cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cl.Module.Attributes, "extern") &&
        member != null && Attributes.Contains(member.Attributes, "extern")) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.Module.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(cl.Module.CompileName);
      } else {
        if (this.ModuleName == cl.Module.CompileName) {
          return IdName(cl);
        } else {
          return cl.Module.CompileName + "." + IdName(cl);
        }
      }
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("_this");
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, bool inLetExprBody, TargetWriter wr) {
      Contract.Requires(thn.Type != null);

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
      var dtName = IdName(dt);
      var ctorName = ctor.CompileName;
      

      if (dt is TupleTypeDecl) {
        wr.Write("dafny.TupleOf({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate:  Dt{Dt_Ctor{arguments}}
        wr.Write("{0}{{{1}{0}_{2}{{{3}}}}}",
          dtName, dt is IndDatatypeDecl ? "" : "&", ctorName,
          arguments);
      } else {
        // Co-recursive call
        // Generate:  Companion_Dt_.LazyDt(func () Dt => Companion_Dt_.CreateCtor(args))
        var companionName = TypeName_Companion(dt, wr, dt.tok);
        wr.Write("{0}.{1}(func () {2} ", companionName, FormatLazyConstructorName(dt.CompileName), IdName(dt), dtName);
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
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          compiledName = string.Format("Len({0})", idParam == null ? 0 : (int) idParam);
          if (id == SpecialField.ID.ArrayLengthInt) {
            postString = ".Int()";
          }
          break;
        case SpecialField.ID.Floor:
          compiledName = "toBigNumber()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "_dafny.BigOrdinal.IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "_dafny.BigOrdinal.IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "_dafny.BigOrdinal.Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "_dafny.BigOrdinal.IsNat(";
          postString = ")";
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

    protected override void EmitMemberSelect(MemberDecl member, bool isLValue, TargetWriter wr) {
      if (member is DatatypeDestructor dtor) {
        if (dtor.EnclosingClass is TupleTypeDecl) {
          wr.Write(".Index(dafny.IntOf({0})).Interface()", dtor.Name);
        } else {
          wr.Write(".{0}()", FormatDatatypeDestructorName(dtor.CompileName));
        }
      } else if (!isLValue && member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        if (compiledName.Length != 0) {
          wr.Write(".{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
        }
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        // sf2 is needed here only because the scope rules for these pattern matches are asinine: sf is *still in scope* but it's useless because it may not have been assigned to!

        // FIXME This is a pretty awful string hack.
        wr.Write(".{0}()", FormatDatatypeConstructorCheckName(fieldName.Substring(3)));
      } else {
        wr.Write(".{0}", IdName(member));
      }
    }

    protected override void EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      foreach (var index in indices) {
        wr.Write(".Index({0}).Interface().({1})", index, TypeName(elmtType, wr, Bpl.Token.NoToken));
      }
    }

    protected override void EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      wr.Write(".Index(");
      var sep = "";
      foreach (var index in indices) {
        wr.Write(sep);
        TrParenExpr(index, wr, inLetExprBody);
        sep = ", ";
      }
      wr.Write(").Interface().({0})", TypeName(elmtType, wr, Bpl.Token.NoToken));
    }

    protected override void EmitArraySelectAsLvalue(string array, List<string> indices, Type elmtType, TargetWriter wr) {
      wr.Write("*({0}.Index({1}).Addr().Interface().(*{2}))", array, Util.Comma(indices), TypeName(elmtType, wr, Bpl.Token.NoToken));
    }

    protected override void EmitArrayUpdate(List<string> indices, string rhs, Type elmtType, TargetWriter wr) {
      wr.Write(".Index({0}).Set(refl.ValueOf({1}))", Util.Comma(indices), rhs);
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr) {
      if (expr is LiteralExpr lit) {
        wr.Write(lit.Value.ToString());
      } else {
        if (AsNativeType(expr.Type) == null) {
          wr.Write("int(");
        }
        TrParenExpr(expr, wr, inLetExprBody);
        if (AsNativeType(expr.Type) == null) {
          wr.Write(".Int64())");
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      var type = source.Type.NormalizeExpand();
      if (type is SeqType || type is SetType) {
        wr.Write(".Index(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(").Interface().({0})", TypeName(source.Type.TypeArgs[0], wr, null));
      } else if (type is MultiSetType) {
        wr.Write(".Multiplicity(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(")");
      } else {
        Contract.Assert(type is MapType);
        // map or imap
        wr.Write(".Get(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(").({0})", TypeName(source.Type.TypeArgs[1], wr, null));
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".Update(");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".");
      if (lo == null) {
        if (hi == null) {
          wr.Write("SliceAll()");
        } else {
          wr.Write("SliceTo(");
          TrExpr(hi, wr, inLetExprBody);
          wr.Write(")");
        }
      } else {
        if (hi == null) {
          wr.Write("SliceFrom(");
          TrExpr(lo, wr, inLetExprBody);
          wr.Write(")");
        } else {
          wr.Write("Slice(");
          TrExpr(lo, wr, inLetExprBody);
          wr.Write(", ");
          TrExpr(hi, wr, inLetExprBody);
          wr.Write(")");
        }
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
      var eeType = expr.E.Type.NormalizeExpand();
      if (eeType is SeqType) {
        TrParenExpr("dafny.MultiSetFromSeq", expr.E, wr, inLetExprBody);
      } else if (eeType is SetType) {
        TrParenExpr("dafny.MultiSetFromSet", expr.E, wr, inLetExprBody);
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

      wr.Write(") {0} {{", TypeName(type, wr, tok));
      var w = EmitReturnExpr(wr);
      wr.Write("})");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr) {
      wr.Write("{0}.{1}()", source, FormatDatatypeConstructorCheckName(ctor.CompileName));
    }
    
    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, TargetWriter wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("({0}).Index({1}).Interface().({2})", source, formalNonGhostIndex, TypeName(dtor.Type, wr, Bpl.Token.NoToken));
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        wr.Write("({0}).{1}()", source, FormatDatatypeDestructorName(dtorName));
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      wr.Write("func (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1} {2}", i == 0 ? "" : ", ", inNames[i], TypeName(inTypes[i], wr, tok));
      }
      var w = wr.NewNamedBlock(") {0}", TypeName(resultType, wr, tok));
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewNamedBlock("function ({0})", bvName);
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      w.Indent();
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;
      TrParenExpr(source, wr, inLetExprBody);
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewNamedBlock("function ({0})", bvName);
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      w.Indent();
      w.Write("return ");
      w.BodySuffix = ";" + w.NewLine;
      wr.Write("({0})", source);
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      var w = wr.NewBlock("func () " + TypeName(resultType, wr, resultTok), "()");
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
      return w;
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      var w = wr.NewNamedBlock("function ({0})", bvName);
      w.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Nothing);
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

    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null;
    }

    bool IsOrderedByCmp(Type t) {
      return t.IsIntegerType || t.IsRealType || t.IsBitVectorType;
    }

    bool IsComparedByEquals(Type t) {
      return t.IsArrayType;
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
            } else if (IsOrderedByCmp(e0.Type)) {
              callString = "Cmp";
              postOpString = " == 0";
            } else if (IsComparedByEquals(e0.Type)) {
              callString = "Equals";
            }else if (IsDirectlyComparable(e0.Type)) {
              opString = "==";
            } else {
              staticCallString = "dafny.AreEqual";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
              postOpString = "/* handle */";
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
              staticCallString = "dafny.AreEqual";
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
          if (AsNativeType(resultType) != null) {
            opString = "<<";
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            callString = "Lsh";
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (AsNativeType(resultType) != null) {
            opString = ">>";
            if (AsNativeType(e1.Type) == null) {
              postOpString = ".Uint64()";
            }
          } else {
            callString = "Rsh";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (AsNativeType(resultType) != null) {
            opString = "+";
            if (resultType.IsBitVectorType) {
              truncateResult = true;
            }
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
              staticCallString =  "dafny.Div_" + GetNativeTypeName(AsNativeType(resultType));
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
              staticCallString = "dafny.Mod_" + GetNativeTypeName(AsNativeType(resultType));
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
      wr.Write("{0}.isZero()", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("dafny.RealOfFrac(");
          TargetWriter w;
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("dafny.IntOf(int64(");
            w = wr.Fork();
            wr.Write("))");
          } else {
            w = wr;
          }
          TrParenExpr(e.E, w, inLetExprBody);
          wr.Write(", dafny.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write("dafny.Char(");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int64())");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
           TrExpr(e.E, wr, inLetExprBody);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("dafny.IntOf(int64(");
              TrExpr(e.E, wr, inLetExprBody);
              wr.Write("))");
            } else {
              // char -> native
              wr.Write("(rune) ");
              TrParenExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            TrExpr(e.E, wr, inLetExprBody);
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("dafny.IntOf(int64(");
            TrExpr(e.E, wr, inLetExprBody);
            wr.Write("))");
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("(" + literal  + ")");
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              TrParenExpr(u.E, wr, inLetExprBody);
              wr.Write(".length");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              TrParenExpr(m.Obj, wr, inLetExprBody);
              wr.Write(".length");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody);
              wr.Write(".Int64()");
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
          wr.Write("dafny.RatToInt");
          TrParenExpr(e.E, wr, inLetExprBody);
          if (AsNativeType(e.ToType) != null) {
            wr.Write(".Int64()");
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

    protected override TargetWriter EmitCoercionIfNecessary(Type from, Type to, Bpl.IToken tok, TargetWriter wr) {
      if (from == null || to == null) {
        return wr;
      }

      from = from.NormalizeExpand();
      to = to.NormalizeExpand();
      if (from.IsTypeParameter || to.IsTypeParameter || EqualsUpToParameters(from, to)) {
        // do nothing
        return wr;
      } else if (Type.IsSupertype(to, from)) {
        // upcast
        var w = wr.Fork();
        wr.Write(".{0}", ClassName(to, wr, tok));
        return w;
      } else if (Type.IsSupertype(from, to)) {
        // downcast (allowed?)
        var w = wr.Fork();
        if (from is UserDefinedType fromUdt && fromUdt.ResolvedClass.ViewAsClass is TraitDecl trait) {
          wr.Write(".{0}.({1})", TypeName_TraitInterface(from, wr, tok), TypeName(to, wr, tok));
        } else {
          wr.Write(".({1})", TypeName(to, wr, tok));
        }
        return w;
      } else {
        Error(tok, "Cannot convert from {0} to {1}", wr, from, to);
        return wr;
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("dafny.SetOf");
        TrExprList(elements, wr, inLetExprBody);
      } else if (ct is MultiSetType) {
        wr.Write("dafny.MultiSetOf");
        TrExprList(elements, wr, inLetExprBody);
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        wr.Write("dafny.SeqOf(");
        var wrElements = wr.Fork();
        wr.Write(")");
        string sep = "";
        foreach (var e in elements) {
          wrElements.Write(sep);
          TrExpr(e, wrElements, inLetExprBody);
          sep = ", ";
        }
      }
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("dafny.NewMapBuilder()");
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
        wr.Write("dafny.NewMapBuilder()");
      } else if (ct is SetType || ct is MultiSetType) {
        wr.Write("dafny.NewBuilder()");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      wr.Indent();
      wr.Write("{0}.Add(", collName);
      TrExpr(elmt, wr, inLetExprBody);
      wr.WriteLine(")");
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr) {
      wr.Indent();
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

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      TrParenExpr("dafny.SingleValue", e, wr, inLetExprBody);
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (!DafnyOptions.O.RunAfterCompile || callToMain == null) {
        // compile now
        return SendToNewGoProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames, outputWriter);
      } else {
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'node'
        // will run the program.
        return true;
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      return SendToNewGoProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames, outputWriter);
    }

    bool SendToNewGoProcess(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      TextWriter outputWriter) {
      Contract.Requires(targetFilename != null && otherFileNames.Count == 0);

      var args = "run " + targetFilename;
      var psi = new ProcessStartInfo("go", args) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = false,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };
      psi.EnvironmentVariables.Add("GOPATH", GoPath(targetFilename));

      try {
        using (var process = Process.Start(psi)) {
          process.WaitForExit();
          return process.ExitCode == 0;
        }
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start go ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }

    static string GoPath(string filename) {
      // Filename is Foo-go/src/Foo.go, so go two directories up
      return Path.GetFullPath(Path.GetDirectoryName(Path.GetDirectoryName(filename)));
    }
  }
}
