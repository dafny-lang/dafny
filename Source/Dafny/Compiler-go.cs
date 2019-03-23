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
      wr.WriteLine("    dafny \"dafny\"");
      wr.WriteLine("    fmt \"fmt\"");
      wr.WriteLine("    refl \"reflect\"");
      wr.Append(ImportWriter);
      wr.WriteLine(")");
      wr.WriteLine("var _ dafny.Char");
      wr.WriteLine("var _ fmt.Stringer");
      wr.WriteLine("var _ refl.Type");
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
      return wr.NewBlock("func main()");
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
        foreach (var tp in typeParameters) {
          if (tp.Characteristics.MustSupportZeroInitialization) {
            instanceFieldWriter.Indent();
            instanceFieldWriter.WriteLine("this.{0} = {0};", "rtd$_" + tp.CompileName);
          }
        }
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
      Error(iter.tok, "Iterators not implemented for Go", wr);
      return wr.NewBlock("_error__iterator__ {0}", iter.Name);
    }

    protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      // ===== For inductive datatypes:
      //
      // $module.Dt = class Dt {
      //   constructor(tag) {
      //     this.$tag = tag;
      //   }
      //   static create_Ctor0(field0, field1, ...) {
      //     let $dt = new Dt(0);
      //     $dt.field0 = field0;
      //     $dt.field1 = field1;
      //     ...
      //     return $dt;
      //   }
      //   static create_Ctor1(...) {
      //     let $dt = new Dt(1);
      //     ...
      //   }
      //   ...
      //
      //   get is_Ctor0 { return this.$tag === 0; }
      //   get is_Ctor1 { return this.$tag === 1; }
      //   ...
      //
      //   static get AllSingletonConstructors() {
      //     return this.AllSingletonConstructors_();
      //   }
      //   static *AllSingletonConstructors_() {
      //     yield Berry.create_Ctor0();
      //     ...
      //   }
      //
      //   get dtor_Dtor0() { return this.Dtor0; }
      //   get dtor_Dtor1() { return this.Dtor1; }
      //   ...
      //
      //   toString() {
      //     ...
      //   }
      //   equals(other) {
      //     ...
      //   }
      //   static Rtd(rtd...) {
      //     return class {
      //       static get Default() { return Dt.create_CtorK(...); }
      //     };
      //   }
      // }
      //
      // ===== For co-inductive datatypes:
      //
      // $module.Dt = class Dt {
      //   constructor(tag) {
      //     this.$tag = tag;
      //   }
      //   _D() {
      //     if (this._d === undefined) {
      //       this._d = this._initializer(this);
      //       delete this._initializer;
      //     }
      //     return this._d;
      //   }
      //   static create_Ctor0($dt, field0, field1, ...) {
      //     if ($dt === null) {
      //       $dt = new Dt(0);
      //       $dt._d = $dt;
      //     }
      //     $dt.field0 = field0;
      //     $dt.field1 = field1;
      //     ...
      //     return $dt;
      //   }
      //   static lazy_Ctor0(initializer) {
      //     let dt = new Dt(0);
      //     dt._initializer = initializer;
      //     return dt;
      //   }
      //   static create_Ctor1(initializer) {
      //     let $dt = new Dt(1);
      //     ...
      //   }
      //   ...
      //
      //   get is_Ctor0() { return this.$tag === 0; }
      //   get is_Ctor1() { return this.$tag === 1; }
      //   ...
      //
      //   static get AllSingletonConstructors() {
      //     return this.AllSingletonConstructors_();
      //   }
      //   static *AllSingletonConstructors_() {
      //     yield Berry.create_Ctor0(null);
      //     ...
      //   }
      //
      //   get dtor_Dtor0() { return this._D().Dtor0; }
      //   get dtor_Dtor1() { return this._D().Dtor1; }
      //   ...
      //
      //   toString() {
      //     if ($tag == 0) {
      //       return "module.Dt.Ctor0";
      //     } else if ...
      //   }
      //   equals(other) {
      //     ...
      //   }
      //   static Rtd(rtd...) {
      //     return class {
      //       static get Default() { return Dt.create_CtorK(...); }
      //     };
      //   }
      // }
      if (dt is TupleTypeDecl) {
        // Tuple types are declared once and for all in DafnyRuntime.js
        return;
      }

      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);

      wr.Indent();
      // from here on, write everything into the new block created here:
      wr = wr.NewNamedBlock("$module.{0} = class {0}", DtT_protected);

      wr.Indent();
      wr.WriteLine("constructor(tag) { this.$tag = tag; }");

      if (dt is CoDatatypeDecl) {
        wr.Indent();
        using (var w0 = wr.NewBlock("_D()")) {
          using (var w1 = EmitIf("this._d === undefined", false, w0)) {
            w1.Indent();
            w1.WriteLine("this._d = this._initializer(this);");
            w1.Indent();
            w1.WriteLine("delete this._initializer;");
          }
          w0.Indent();
          w0.WriteLine("return this._d");
        }
      }

      // query properties
      var i = 0;
      foreach (var ctor in dt.Ctors) {
        // collect the names of non-ghost arguments
        var argNames = new List<string>();
        var k = 0;
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            argNames.Add(FormalName(formal, k));
            k++;
          }
        }
        // datatype:
        //   static create_Ctor0(params) { let $dt = new Dt(tag); $dt.param0 = param0; ...; return $dt; }
        // codatatype:
        //   static create_Ctor0(params) { if ($dt === null) { $dt = new Dt(tag); $dt._d = $dt; } $dt.param0 = param0; ...; return $dt; }
        //   static lazy_Ctor0(initializer) { let dt = new Dt(tag); dt._initializer = initializer; return dt; }
        wr.Indent();
        wr.Write("static create_{0}(", ctor.CompileName);
        if (dt is CoDatatypeDecl) {
          wr.Write("$dt{0}", argNames.Count == 0 ? "" : ",");
        }
        wr.Write(Util.Comma(argNames, nm => nm));
        var w = wr.NewBlock(")");
        if (dt is CoDatatypeDecl) {
          var wThen = EmitIf("$dt === null", false, w);
          wThen.Indent();
          wThen.WriteLine("$dt = new {0}({1});", DtT_protected, i);
          wThen.Indent();
          wThen.WriteLine("$dt._d = $dt;");
        } else {
          w.Indent();
          w.WriteLine("let $dt = new {0}({1});", DtT_protected, i);
        }
        foreach (var arg in argNames) {
          w.Indent();
          w.WriteLine("$dt.{0} = {0};", arg);
        }
        w.Indent();
        w.WriteLine("return $dt;");
        if (dt is CoDatatypeDecl) {
          wr.Indent();
          var wBody = wr.NewNamedBlock("static lazy_{0}(initializer)", ctor.CompileName);
          wBody.Indent();
          wBody.WriteLine("let dt = new {0}({1});", DtT_protected, i);
          wBody.Indent();
          wBody.WriteLine("dt._initializer = initializer;");
          wBody.Indent();
          wBody.WriteLine("return dt;");
        }
        i++;
      }

      // query properties
      i = 0;
      foreach (var ctor in dt.Ctors) {
        // get is_Ctor0() { return _D is Dt_Ctor0; }
        wr.Indent();
        wr.WriteLine("get is_{0}() {{ return this.$tag === {1}; }}", ctor.CompileName, i);
        i++;
      }

      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        wr.Indent();
        using (var w = wr.NewNamedBlock("static get AllSingletonConstructors()")) {
          w.Indent();
          w.WriteLine("return this.AllSingletonConstructors_();");
        }
        wr.Indent();
        using (var w = wr.NewNamedBlock("static *AllSingletonConstructors_()")) {
          foreach (var ctor in dt.Ctors) {
            Contract.Assert(ctor.Formals.Count == 0);
            w.Indent();
            w.WriteLine("yield {0}.create_{1}({2});", DtT_protected, ctor.CompileName, dt is CoDatatypeDecl ? "null" : "");
          }
        }
      }
      
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              // datatype:   get dtor_Dtor0() { return this.Dtor0; }
              // codatatype: get dtor_Dtor0() { return this._D().Dtor0; }
              wr.Indent();
              wr.WriteLine("get dtor_{0}() {{ return this{2}.{1}; }}", arg.CompileName, IdName(arg), dt is CoDatatypeDecl ? "._D()" : "");
            }
          }
        }
      }

      if (dt is CoDatatypeDecl) {
        // toString method
        wr.Indent();
        var w = wr.NewBlock("toString()");
        i = 0;
        foreach (var ctor in dt.Ctors) {
          using (var thn = EmitIf(string.Format("this.$tag === {0}", i), true, w)) {
            thn.Indent();
            var nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
            thn.WriteLine("return \"{0}\";", nm);
          }
          i++;
        }
        using (var els = w.NewBlock("")) {
          els.Indent();
          els.WriteLine("return \"{0}.{1}.unexpected\";", dt.Module.CompileName, DtT);
        }

      } else if (dt is IndDatatypeDecl && !(dt is TupleTypeDecl)) {
        // toString method
        wr.Indent();
        using (var w = wr.NewBlock("toString()")) {
          i = 0;
          foreach (var ctor in dt.Ctors) {
            var cw = EmitIf(string.Format("this.$tag === {0}", i), true, w);
            cw.Indent();
            var nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
            cw.Write("return \"{0}\"", nm);
            var sep = " + \"(\" + ";
            var anyFormals = false;
            var k = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                anyFormals = true;
                cw.Write("{0}_dafny.toString(this.{1})", sep, FormalName(arg, k));
                sep = " + \", \" + ";
                k++;
              }
            }
            if (anyFormals) {
              cw.Write(" + \")\"");
            }
            cw.WriteLine(";");
            i++;
          }
          var wElse = w.NewBlock("");
          wElse.Indent();
          wElse.WriteLine("return \"<unexpected>\";");
        }
      }

      // equals method
      wr.Indent();
      using (var w = wr.NewBlock("equals(other)")) {
        using (var thn = EmitIf("this === other", true, w)) {
          EmitReturnExpr("true", thn);
        }
        i = 0;
        foreach (var ctor in dt.Ctors) {
          var thn = EmitIf(string.Format("this.$tag === {0}", i), true, w);
          var guard = EmitReturnExpr(thn);
          guard.Write("other.$tag === {0}", i);
          var k = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              string nm = FormalName(arg, k);
              if (IsDirectlyComparable(arg.Type)) {
                guard.Write(" && this.{0} === other.{0}", nm);
              } else {
                guard.Write(" && _dafny.areEqual(this.{0}, other.{0})", nm);
              }
              k++;
            }
          }
          i++;
        }
        using (var els = w.NewBlock("")) {
          els.Indent();
          els.WriteLine("return false; // unexpected");
        }
      }

      // Note: It is important that the following be a class with a static getter Default(), as opposed
      // to a simple "{ Default: ... }" object, because we need for any recursive calls in the default
      // expression to be evaluated lazily. (More precisely, not evaluated at all, but that will sort
      // itself out due to the restrictions placed by the resolver.)
      //
      // static Rtd(rtd...) {
      //   return class {
      //     static get Default() { return Dt.create_CtorK(...); }
      //   };
      // }
      wr.Indent();
      wr.Write("static Rtd(");
      WriteRuntimeTypeDescriptorsFormals(UsedTypeParameters(dt), true, wr);
      using (var wRtd = wr.NewBlock(")")) {
        wRtd.Indent();
        using (var wClass = wRtd.NewBlock("return class", ";")) {
          wClass.Indent();
          using (var wDefault = wClass.NewBlock("func Rtd_default() Rtd")) {
            wDefault.Indent();
            wDefault.Write("return ");
            DatatypeCtor defaultCtor;
            if (dt is IndDatatypeDecl) {
              defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
            } else {
              defaultCtor = ((CoDatatypeDecl)dt).Ctors[0];  // pick any one of them (but pick must be the same as in InitializerIsKnown and HasZeroInitializer)
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
            wDefault.WriteLine(";");
          }
        }
      }
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
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Indent();
          wr.Write("{0} string", "rtd$_" + tp.CompileName);
        }
      }
      return c;
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
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);

      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as bool, since no particular type information is apparently needed for this type
        return "_dafny.Rtd_bool";
      }

      if (xType is BoolType) {
        return "_dafny.Rtd_bool";
      } else if (xType is CharType) {
        return "_dafny.Rtd_char";
      } else if (xType is IntType) {
        return "_dafny.Rtd_int";
      } else if (xType is BigOrdinalType) {
        return "_dafny.BigOrdinal";
      } else if (xType is RealType) {
        return "_dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        if (t.NativeType != null) {
          return "_dafny.Rtd_bv_Native";
        } else {
          return "_dafny.Rtd_bv_NonNative";
        }
      } else if (xType is SetType) {
        return "_dafny.Set";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSet";
      } else if (xType is SeqType) {
        return "_dafny.Seq";
      } else if (xType is MapType) {
        return "_dafny.Map";
      } else if (xType.IsBuiltinArrowType) {
        return "_dafny.Rtd_ref";  // null suffices as a default value, since the function will never be called
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        var tp = udt.ResolvedParam;
        if (tp != null) {
          return string.Format("{0}rtd$_{1}", tp.Parent is ClassDecl ? "this." : "", tp.CompileName);
        }
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "_dafny.Rtd_ref";
        } else if (cl is ClassDecl) {
          return "_dafny.Rtd_ref";
        } else if (cl is DatatypeDecl) {
          var dt = (DatatypeDecl)cl;
          var w = new TargetWriter();
          w.Write("{0}.Rtd(", dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt));
          EmitRuntimeTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), cl.TypeArgs, udt.tok, true, w);
          w.Write(")");
          return w.ToString();
        } else if (xType.IsNonNullRefType) {
          // this initializer shouldn't ever be needed; the compiler is expected to generate an error
          // sooner or later, , but it could be that the the compiler needs to
          // lay down some bits to please the C#'s compiler's different definite-assignment rules.
          return "_dafny.Rtd_ref/*not used*/";
        } else {
          Contract.Assert(cl is NewtypeDecl || cl is SubsetTypeDecl);
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok);
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
      instanceFieldWriter.Indent();
      instanceFieldWriter.WriteLine("{0}", TypeName(superType, instanceFieldWriter, tok));

      instanceFieldInitWriter.Indent();
      instanceFieldInitWriter.WriteLine("{0}: {1}(),", ClassName(superType, instanceFieldInitWriter, tok), TypeName_Constructor(superType, instanceFieldInitWriter, tok));

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
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
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
        } else if (udt.IsTypeParameter) {
          return "interface{}";
        }
        return TypeName_UDT(s, udt.TypeArgs, wr, udt.tok);
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "dafny.Array";
      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return "_dafny.Map";
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
        return "_dafny.Set.Empty";
      } else if (xType is MultiSetType) {
        return "_dafny.MultiSet.Empty";
      } else if (xType is SeqType) {
        return "_dafny.Seq.of()";
      } else if (xType is MapType) {
        return "_dafny.Map.Empty";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization) {
          return "undefined";
        } else {
          return string.Format("{0}.Default", RuntimeTypeDescriptor(udt, udt.tok, wr));
        }
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
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            if (arrayClass.Dims == 1) {
              return "[]";
            } else {
              return string.Format("_dafny.newArray(undefined, {0})", Util.Comma(arrayClass.Dims, _ => "0"));
            }
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
        var dt = (DatatypeDecl)cl;
        var s = dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt);
        var w = new TargetWriter();
        w.Write("{0}.Rtd(", s);
        EmitRuntimeTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), dt.TypeArgs, udt.tok, true, w);
        w.Write(").Default");
        return w.ToString();
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

    protected static string FormatCompanionName(string clsName) =>
      string.Format("Companion_{0}_", clsName);
    protected static string FormatCompanionTypeName(string clsName) =>
      // Note that the initial lowercase means the name isn't exported, but it doesn't need to be
      string.Format("companionStruct_{0}_", clsName);
    protected static string FormatDefaultName(string typeName) =>
      string.Format("Default_{0}_", typeName);
    protected static string FormatGetterName(string propName) =>
      string.Format("Get_{0}_", propName);
    protected static string FormatInitializerName(string clsName) =>
      string.Format("New_{0}_", clsName);
    protected static string FormatSetterName(string propName) =>
      string.Format("Set_{0}_", propName);
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

    protected string TypeName_Constructor(Type type, TextWriter wr, Bpl.IToken tok) {
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

    private TargetWriter/*?*/ DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool includeRhs, TargetWriter wr) {
      wr.Indent();
      wr.Write("var {0}", name);
      
      if (type != null) {
        // Always specify the type in case the rhs is nil
        wr.Write(" {0}", TypeName(type, wr, tok));
      }
      
      TargetWriter w;
      if (includeRhs) {
        wr.Write(" = ");
        w = wr.Fork();
      } else {
        w = null;
      }
      wr.WriteLine();

      wr.Indent();
      wr.WriteLine("var _ = {0}", name);

      return w;
    }

    protected override void DeclareLocalVar(string name, Type type, Bpl.IToken tok, bool leaveRoomForRhs, string rhs, TargetWriter wr) {
      var w = DeclareLocalVar(name, type, tok, includeRhs:(rhs != null || leaveRoomForRhs), wr:wr);
      if (rhs != null) {
        w.Write(rhs);
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, TargetWriter wr) {
      return DeclareLocalVar(name, type, tok, includeRhs:true, wr:wr);
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
      wr.Indent();
      return wr.NewNamedBlock("L{0}:", label);
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
      wr.WriteLine("yield null;");
    }

    protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.Indent();
      wr.WriteLine("throw new Error(\"{0}\");", message);
    }

    protected override BlockTargetWriter CreateWhileLoop(out TargetWriter guardWriter, TargetWriter wr) {
      wr.Indent();
      wr.Write("for (");
      guardWriter = new TargetWriter(wr.IndentLevel);
      wr.Append(guardWriter);
      var wBody = wr.NewBlock(")");
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
      return string.Format("_dafny.Quantifier");
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null) {
      wr.Indent();
      wr.Write("for (const {0} of ", boundVar);
      collectionWriter = new TargetWriter(wr.IndentLevel);
      wr.Append(collectionWriter);
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      } else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", "{0} = {1};", altBoundVarName, boundVar);
      } else {
        return wr.NewBlockWithPrefix(")", "let {0} = {1};", altBoundVarName, boundVar);
      }
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      var cl = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
      if (cl != null) {
        if (cl.Name == "object") {
          wr.Write("new(struct{})");
        } else {
          wr.Write("{0}()", TypeName_Constructor(type, wr, tok));
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
        wr.Write("null");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("'{0}'", v == "\\0" ? "\\u0000" : v);  // JavaScript doesn't have a \0
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("dafny.NewArrayFromString(");
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
      wr.Write("{0}.push(_dafny.Tuple.of(", ingredients, tupleTypeArgs);
      var wrTuple = new TargetWriter(wr.IndentLevel);
      wr.Append(wrTuple);
      wr.WriteLine("));");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write("{0}[{1}]", prefix, i);
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
      var dtName = dt.FullCompileName;
      var ctorName = ctor.CompileName;

      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.Tuple.of({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate:  Dt.create_Ctor(arguments)
        wr.Write("{0}.create_{1}({2}{3})",
          dtName, ctorName,
          dt is IndDatatypeDecl ? "" : arguments.Length == 0 ? "null" : "null, ",
          arguments);
      } else {
        // Co-recursive call
        // Generate:  Dt.lazy_Ctor(($dt) => Dt.create_Ctor($dt, args))
        wr.Write("{0}.lazy_{1}(($dt) => ", dtName, ctorName);
        wr.Write("{0}.create_{1}($dt{2}{3})", dtName, ctorName, arguments.Length == 0 ? "" : ", ", arguments);
        wr.Write(")");
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
          compiledName = string.Format("Len(dafny.IntOf({0}))", idParam == null ? 0 : (int) idParam);
          if (id == SpecialField.ID.ArrayLengthInt) {
            preString = "int(";
            postString = ".Int64())";
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
          compiledName = "Keys";
          break;
        case SpecialField.ID.Values:
          compiledName = "Values";
          break;
        case SpecialField.ID.Items:
          compiledName = "Items";
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
      if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl) {
        wr.Write("[{0}]", dtor.Name);
      } else if (!isLValue && member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        if (compiledName.Length != 0) {
          wr.Write(".{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
        }
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
      if (source.Type.NormalizeExpand() is SeqType) {
        // seq
        wr.Write(".Index(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(").Interface().({0})", TypeName(source.Type.TypeArgs[0], wr, null));
      } else {
        // map or imap
        wr.Write(".get(");
        TrExpr(index, wr, inLetExprBody);
        wr.Write(")");
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".update(");
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
      TrParenExpr("_dafny.MultiSet.FromArray", expr.E, wr, inLetExprBody);
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

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, TargetWriter wr) {
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        wr.Write("({0})[{1}]", source, formalNonGhostIndex);
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        wr.Write("({0}){1}.{2}", source, ctor.EnclosingDatatype is CoDatatypeDecl ? "._D()" : "", dtorName);
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr) {
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
      var w = wr.NewBlock("function ()", "()");
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
          if (expr.Type.AsMultiSetType != null) {
            TrParenExpr(expr, wr, inLetExprBody);
            wr.Write(".Cardinality()");
          } else {
            TrExpr(expr, wr, inLetExprBody);
            wr.Write(".Len(dafny.Zero)");
          }
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
              staticCallString = "refl.DeepEquals";
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
              staticCallString = "refl.DeepEquals";
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
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersect"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          staticCallString = "_dafny.Seq.IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          staticCallString = "_dafny.Seq.IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = "_dafny.Seq.Concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          staticCallString = "_dafny.Seq.contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!"; callString = "contains"; reverseArguments = true; break;

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
          wr.Write("(Char) ");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".Int64()");
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
      if (EqualsUpToParameters(from, to)) {
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
        wr.Write("_dafny.Set.fromElements");
        TrExprList(elements, wr, inLetExprBody);
      } else if (ct is MultiSetType) {
        wr.Write("_dafny.MultiSet.fromElements");
        TrExprList(elements, wr, inLetExprBody);
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        var wrElements = new TargetWriter(wr.IndentLevel);
        wr.Write("dafny.NewArrayWithValues(refl.ValueOf({0}).Type(), ", TypeInitializationValue(ct.Arg, wr, tok, false), wrElements);
        wr.Append(wrElements);
        wr.Write(")");
        string sep = "";
        foreach (var e in elements) {
          wrElements.Write(sep + "refl.ValueOf");
          TrParenExpr(e, wrElements, inLetExprBody);
          sep = ", ";
        }
      }
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("_dafny.Map.of(");
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("[");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(",");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write("]");
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("new _dafny.Set()");
      } else if (ct is MultiSetType) {
        wr.Write("new _dafny.MultiSet()");
      } else if (ct is MapType) {
        wr.Write("new _dafny.Map()");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      wr.Indent();
      wr.Write("{0}.add(", collName);
      TrExpr(elmt, wr, inLetExprBody);
      wr.WriteLine(");");
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr) {
      wr.Indent();
      wr.Write("{0}.push([", collName);
      var termLeftWriter = new TargetWriter(wr.IndentLevel);
      wr.Append(termLeftWriter);
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine("]);");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      // collections are built in place
      return collName;
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody);
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
