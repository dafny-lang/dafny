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
using System.Text;
using System.Threading.Tasks;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Compilers {
  public class JavaScriptCompiler : SinglePassCompiler {
    public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".js" };

    public override string TargetLanguage => "JavaScript";
    public override string TargetExtension => "js";

    public override bool SupportsInMemoryCompilation => true;
    public override bool TextualTargetIsExecutable => true;

    public override IReadOnlySet<string> SupportedNativeTypes =>
      new HashSet<string>(new List<string> { "number" });

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.MethodSynthesis,
      Feature.ExternalConstructors,
      Feature.SubsetTypeTests
    };

    const string DafnySetClass = "_dafny.Set";
    const string DafnyMultiSetClass = "_dafny.MultiSet";
    const string DafnySeqClass = "_dafny.Seq";
    const string DafnyMapClass = "_dafny.Map";

    static string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter || tp is OpaqueTypeDecl);
      return $"_default_{tp.CompileName}";
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("// Dafny program {0} compiled into JavaScript", program.Name);
      ReadRuntimeSystem(program, "DafnyRuntime.js", wr);
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      Coverage.EmitSetup(wr);
      wr.WriteLine($"_dafny.HandleHaltExceptions(() => {mainMethod.EnclosingClass.FullCompileName}.{(mainMethod.IsStatic ? IdName(mainMethod) : "Main")}(_dafny.{CharMethodQualifier}FromMainArguments(require('process').argv)));");
      Coverage.EmitTearDown(wr);
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var wr = (cw as JavaScriptCompiler.ClassWriter).MethodWriter;
      return wr.NewBlock($"static Main({argsParameterName})");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, ConcreteSyntaxTree wr) {
      if (!isExtern || libraryName != null) {
        wr.Write("let {0} = ", moduleName);
      }

      string footer = ")(); // end of module " + moduleName;
      var block = wr.NewBlock("(function()", footer);
      var beforeReturnBody = block.Fork(0);
      if (!isExtern) {
        // create new module here
        beforeReturnBody.WriteLine("let $module = {};");
      } else if (libraryName == null) {
        // extend a module provided in another .js file
        beforeReturnBody.WriteLine("let $module = {0};", moduleName);
      } else {
        // require a library
        beforeReturnBody.WriteLine("let $module = require(\"{0}\");", libraryName);
      }
      block.WriteLine("return $module;");
      return beforeReturnBody;
    }

    protected override string GetHelperModuleName() => "_dafny";

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string/*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}" + (isExtern ? " extends $module.{0}" : ""), name), ";");
      w.Write("constructor (");
      if (typeParameters != null) {
        WriteRuntimeTypeDescriptorsFormals(typeParameters, false, w);
      }
      var fieldWriter = w.NewBlock(")");
      if (isExtern) {
        fieldWriter.Write("super(");
        if (typeParameters != null) {
          WriteRuntimeTypeDescriptorsFormals(typeParameters, false, w);
        }
        fieldWriter.WriteLine(");");
      }
      if (fullPrintName != null) {
        fieldWriter.WriteLine("this._tname = \"{0}\";", fullPrintName);
      }
      if (typeParameters != null) {
        foreach (var tp in typeParameters) {
          if (NeedsTypeDescriptor(tp)) {
            fieldWriter.WriteLine("this.{0} = {0};", "rtd$_" + tp.CompileName);
          }
        }
      }
      if (superClasses != null) {
        superClasses = superClasses.Where(trait => !trait.IsObject).ToList();
        var parentTraitsWriter = w.NewBlock("_parentTraits()");
        parentTraitsWriter.WriteLine("return [{0}];", Util.Comma(superClasses, parent => TypeName(parent, parentTraitsWriter, tok)));
      }
      var methodWriter = w;
      return new ClassWriter(this, methodWriter, fieldWriter);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr) {
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", IdProtect(name)), ";");
      var fieldWriter = w;  // not used for traits, but we need a value to give to the ClassWriter
      var methodWriter = w;
      return new ClassWriter(this, methodWriter, fieldWriter);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      // An iterator is compiled as follows:
      //   public class MyIteratorExample
      //   {
      //     public T q;  // in-parameter
      //     public T x;  // yield-parameter
      //     public int y;  // yield-parameter
      //     IEnumerator<object> _iter;
      //
      //     public void _MyIteratorExample(T q) {
      //       this.q = q;
      //       _iter = TheIterator();
      //     }
      //
      //     public void MoveNext(out bool more) {
      //       more =_iter.MoveNext();
      //     }
      //
      //     private IEnumerator<object> TheIterator() {
      //       // the translation of the body of the iterator, with each "yield" turning into a "yield return null;"
      //       yield break;
      //     }
      //   }

      var cw = CreateClass(IdProtect(iter.EnclosingModuleDefinition.CompileName), IdName(iter), iter, wr) as JavaScriptCompiler.ClassWriter;
      var w = cw.MethodWriter;
      var instanceFieldsWriter = cw.FieldWriter;
      // here come the fields
      Constructor ct = null;
      foreach (var member in iter.Members) {
        var f = member as Field;
        if (f != null && !f.IsGhost) {
          DeclareField(IdName(f), false, false, f.Type, f.tok, PlaceboValue(f.Type, instanceFieldsWriter, f.tok, true), instanceFieldsWriter);
        } else if (member is Constructor) {
          Contract.Assert(ct == null);  // we're expecting just one constructor
          ct = (Constructor)member;
        }
      }
      Contract.Assert(ct != null);  // we do expect a constructor
      instanceFieldsWriter.WriteLine("this._iter = undefined;");

      // here's the initializer method
      w.Write("{0}(", IdName(ct));
      string sep = "";
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          // here we rely on the parameters and the corresponding fields having the same names
          w.Write("{0}{1}", sep, IdName(p));
          sep = ", ";
        }
      }
      {
        var wBody = w.NewBlock(")");
        foreach (var p in ct.Ins) {
          if (!p.IsGhost) {
            wBody.WriteLine("this.{0} = {0};", IdName(p));
          }
        }
        wBody.WriteLine("this.__iter = this.TheIterator();");
      }
      // here are the enumerator methods
      {
        var wBody = w.NewBlock("MoveNext()");
        wBody.WriteLine("let r = this.__iter.next();");
        wBody.WriteLine("return !r.done;");
      }
      var wIter = w.NewBlock("*TheIterator()");
      wIter.WriteLine("let _this = this;");
      return wIter;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
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
        return null;
      }

      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);
      var simplifiedType = DatatypeWrapperEraser.SimplifyType(UserDefinedType.FromTopLevelDecl(dt.tok, dt));

      // from here on, write everything into the new block created here:
      var btw = wr.NewNamedBlock("$module.{0} = class {0}", DtT_protected);
      wr = btw;

      wr.WriteLine("constructor(tag) { this.$tag = tag; }");

      if (dt is CoDatatypeDecl) {
        var w0 = wr.NewBlock("_D()");
        var w1 = EmitIf("this._d === undefined", false, w0);
        w1.WriteLine("this._d = this._initializer(this);");
        w1.WriteLine("delete this._initializer;");
        w0.WriteLine("return this._d");
      }

      // create methods
      var i = 0;
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
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
        wr.Write("static create_{0}(", ctor.CompileName);
        if (dt is CoDatatypeDecl) {
          wr.Write("$dt{0}", argNames.Count == 0 ? "" : ",");
        }
        wr.Write(Util.Comma(argNames, nm => nm));
        var w = wr.NewBlock(")");
        if (dt is CoDatatypeDecl) {
          var wThen = EmitIf("$dt === null", false, w);
          wThen.WriteLine("$dt = new {0}({1});", DtT_protected, i);
          wThen.WriteLine("$dt._d = $dt;");
        } else {
          w.WriteLine("let $dt = new {0}({1});", DtT_protected, i);
        }
        foreach (var arg in argNames) {
          w.WriteLine("$dt.{0} = {0};", arg);
        }
        w.WriteLine("return $dt;");
        if (dt is CoDatatypeDecl) {
          var wBody = wr.NewNamedBlock("static lazy_{0}(initializer)", ctor.CompileName);
          wBody.WriteLine("let dt = new {0}({1});", DtT_protected, i);
          wBody.WriteLine("dt._initializer = initializer;");
          wBody.WriteLine("return dt;");
        }
        i++;
      }

      // query properties
      i = 0;
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        // get is_Ctor0() { return _D is Dt_Ctor0; }
        wr.WriteLine("get is_{0}() {{ return this.$tag === {1}; }}", ctor.CompileName, i);
        i++;
      }

      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        {
          var w = wr.NewNamedBlock("static get AllSingletonConstructors()");
          w.WriteLine("return this.AllSingletonConstructors_();");
        }
        {
          var w = wr.NewNamedBlock("static *AllSingletonConstructors_()");
          foreach (var ctor in dt.Ctors) {
            Contract.Assert(ctor.Formals.Count == 0);
            if (ctor.IsGhost) {
              w.WriteLine("yield {0};", ForcePlaceboValue(UserDefinedType.FromTopLevelDecl(dt.tok, dt), w, dt.tok));
            } else {
              w.WriteLine("yield {0}.create_{1}({2});", DtT_protected, ctor.CompileName, dt is CoDatatypeDecl ? "null" : "");
            }
          }
        }
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors.Where(dtor => dtor.EnclosingCtors[0] == ctor)) {
          var compiledConstructorCount = dtor.EnclosingCtors.Count(constructor => !constructor.IsGhost);
          if (compiledConstructorCount != 0) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              // datatype:   get dtor_Dtor0() { return this.Dtor0; }
              // codatatype: get dtor_Dtor0() { return this._D().Dtor0; }
              wr.WriteLine("get dtor_{0}() {{ return this{2}.{1}; }}", arg.CompileName, IdName(arg), dt is CoDatatypeDecl ? "._D()" : "");
            }
          }
        }
      }

      if (dt is CoDatatypeDecl) {
        // toString method
        var w = wr.NewBlock("toString()");
        i = 0;
        foreach (var ctor in dt.Ctors) {
          var thn = EmitIf(string.Format("this.$tag === {0}", i), true, w);
          var nm = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") +
                   dt.Name + "." + ctor.Name;
          thn.WriteLine("return \"{0}\";", nm);
          i++;
        }
        var els = w.NewBlock("");
        els.WriteLine("return \"{0}.{1}.unexpected\";", dt.EnclosingModuleDefinition.CompileName, DtT);

      } else if (dt is IndDatatypeDecl && !(dt is TupleTypeDecl)) {
        // toString method
        var w = wr.NewBlock("toString()");
        i = 0;
        foreach (var ctor in dt.Ctors) {
          var cw = EmitIf(string.Format("this.$tag === {0}", i), true, w);
          var nm = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") +
                   dt.Name + "." + ctor.Name;
          cw.Write("return \"{0}\"", nm);
          var sep = " + \"(\" + ";
          var anyFormals = false;
          var k = 0;
          foreach (var arg in ctor.Formals) {
            if (!arg.IsGhost) {
              anyFormals = true;
              if (arg.Type.IsStringType && UnicodeCharEnabled) {
                cw.Write("{0}this.{1}.toVerbatimString(true)", sep, FormalName(arg, k));
              } else {
                cw.Write("{0}_dafny.toString(this.{1})", sep, FormalName(arg, k));
              }

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
        wElse.WriteLine("return \"<unexpected>\";");
      }

      // equals method
      {
        var w = wr.NewBlock("equals(other)");
        {
          var thn = EmitIf("this === other", true, w);
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
              if (IsDirectlyComparable(DatatypeWrapperEraser.SimplifyType(arg.Type))) {
                guard.Write(" && this.{0} === other.{0}", nm);
              } else {
                guard.Write(" && _dafny.areEqual(this.{0}, other.{0})", nm);
              }
              k++;
            }
          }
          i++;
        }
        var els = w.NewBlock("");
        els.WriteLine("return false; // unexpected");
      }

      // static Default(defaultValues...) {  // where defaultValues are the parameters to the grounding constructor
      //   return Dt.create_GroundingCtor(defaultValues...);
      // }
      wr.Write("static Default(");
      wr.Write(UsedTypeParameters(dt).Comma(FormatDefaultTypeParameterValue));
      {
        var wDefault = wr.NewBlock(")");
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
        wDefault.WriteLine(";");
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
      wr.Write("static Rtd(");
      WriteRuntimeTypeDescriptorsFormals(UsedTypeParameters(dt), true, wr);
      var wRtd = wr.NewBlock(")");
      var wClass = wRtd.NewBlock("return class", ";");
      {
        var wDefault = wClass.NewBlock("static get Default()");
        var arguments = Util.Comma(UsedTypeParameters(dt),
          tp => DefaultValue(new UserDefinedType(tp), wDefault, dt.tok, true));
        wDefault.WriteLine($"return {DtT_protected}.Default({arguments});");
      }

      return new ClassWriter(this, btw, btw);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(nt.EnclosingModuleDefinition.CompileName), IdName(nt), nt, wr);
      var w = cw.MethodWriter;
      if (nt.NativeType != null) {
        var wIntegerRangeBody = w.NewBlock("static *IntegerRange(lo, hi)");
        var wLoopBody = wIntegerRangeBody.NewBlock("while (lo.isLessThan(hi))");
        wLoopBody.WriteLine("yield lo.toNumber();");
        EmitIncrementVar("lo", wLoopBody);
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        var wStmts = w.Fork();
        if (nt.NativeType == null) {
          TrExpr(nt.Witness, witness, false, wStmts);
        } else {
          TrParenExpr(nt.Witness, witness, false, wStmts);
          witness.Write(".toNumber()");
        }
        DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString(), w);
      }
      // In JavaScript, the companion class of a newtype (which is what is being declared here) doubles as a
      // type descriptor for the newtype. The Default() method for that type descriptor is declared here.
      var wDefault = w.NewBlock("static get Default()");
      var udt = new UserDefinedType(nt.tok, nt.Name, nt, new List<Type>());
      var d = TypeInitializationValue(udt, wr, nt.tok, false, false);
      wDefault.WriteLine("return {0};", d);
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
      string d;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var sw = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        var wStmts = w.Fork();
        TrExpr(sst.Witness, sw, false, wStmts);
        DeclareField("Witness", true, true, sst.Rhs, sst.tok, sw.ToString(), w);
        d = TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".Witness";
      } else {
        d = TypeInitializationValue(udt, wr, sst.tok, false, false);
      }
      w.NewBlock("static get Default()").WriteLine($"return {d};");
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Number:
          name = "number";
          break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly JavaScriptCompiler Compiler;
      public readonly ConcreteSyntaxTree MethodWriter;
      public readonly ConcreteSyntaxTree FieldWriter;

      public ClassWriter(JavaScriptCompiler compiler, ConcreteSyntaxTree methodWriter, ConcreteSyntaxTree fieldWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(fieldWriter != null);
        this.Compiler = compiler;
        this.MethodWriter = methodWriter;
        this.FieldWriter = fieldWriter;
      }

      public ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.tok, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, MethodWriter, forBodyInheritance, lookasideBody);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }
      public ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, createBody, out setterWriter, MethodWriter);
      }
      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, FieldWriter);
      }
      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();  // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
      }
      public ConcreteSyntaxTree/*?*/ ErrorWriter() => MethodWriter;
      public void Finish() { }
    }

    protected override bool SupportsStaticsInGenericClasses => false;

    protected ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (!createBody) {
        return null;
      }

      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(m);
      wr.Write("{0}{1}(", m.IsStatic || customReceiver ? "static " : "", IdName(m));
      var sep = "";
      WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, m.EnclosingClass, m, lookasideBody), wr, ref sep, tp => $"rtd$_{tp.CompileName}");
      if (customReceiver) {
        var nt = m.EnclosingClass;
        var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, nt);
        DeclareFormal(sep, "_this", receiverType, m.tok, true, wr);
        sep = ", ";
      }
      WriteFormals(sep, m.Ins, wr);
      var w = wr.NewBlock(")");

      if (!m.IsStatic && !customReceiver) {
        w.WriteLine("let _this = this;");
      }
      return w;
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(Method m, ConcreteSyntaxTree wr) {
      var beforeReturnBlock = wr.Fork(0);
      EmitReturn(m.Outs, wr);
      return beforeReturnBlock;
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (!createBody) {
        return null;
      }

      var customReceiver = !forBodyInheritance && NeedsCustomReceiver(member);
      wr.Write("{0}{1}(", isStatic || customReceiver ? "static " : "", name);
      var sep = "";
      var nTypes = WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, lookasideBody), wr, ref sep, tp => $"rtd$_{tp.CompileName}");
      if (customReceiver) {
        var nt = member.EnclosingClass;
        var receiverType = UserDefinedType.FromTopLevelDecl(tok, nt);
        DeclareFormal(sep, "_this", receiverType, tok, true, wr);
        sep = ", ";
      }
      WriteFormals(sep, formals, wr);
      var w = wr.NewBlock(")", ";");
      if (!isStatic && !customReceiver) {
        w.WriteLine("let _this = this;");
      }
      return w;
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, ConcreteSyntaxTree wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || NeedsTypeDescriptor(tp)) {
          wr.Write($"{prefix}rtd$_{tp.CompileName}");
          prefix = ", ";
          c++;
        }
      }
      return c;
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
      Contract.Requires(type != null);
      Contract.Requires(tok != null);
      Contract.Requires(wr != null);

      var xType = DatatypeWrapperEraser.SimplifyType(type, true);
      if (xType is BoolType) {
        return "_dafny.Rtd_bool";
      } else if (xType is CharType) {
        return UnicodeCharEnabled ? "_dafny.Rtd_codepoint" : "_dafny.Rtd_char";
      } else if (xType is IntType) {
        return "_dafny.Rtd_int";
      } else if (xType is BigOrdinalType) {
        return "_dafny.BigOrdinal";
      } else if (xType is RealType) {
        return "_dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        if (t.NativeType != null) {
          return "_dafny.Rtd_number";
        } else {
          return "_dafny.Rtd_int";
        }
      } else if (xType is SetType) {
        return DafnySetClass;
      } else if (xType is MultiSetType) {
        return DafnyMultiSetClass;
      } else if (xType is SeqType) {
        return DafnySeqClass;
      } else if (xType is MapType) {
        return DafnyMapClass;
      } else if (xType.IsBuiltinArrowType) {
        return "_dafny.Rtd_ref";  // null suffices as a default value, since the function will never be called
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        if (udt.ResolvedClass is TypeParameter tp) {
          return string.Format("{0}rtd$_{1}", thisContext != null && tp.Parent is ClassDecl && !(tp.Parent is TraitDecl) ? "this." : "", tp.CompileName);
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
          var w = new ConcreteSyntaxTree();
          w.Write("{0}.Rtd(", dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt));
          EmitTypeDescriptorsActuals(UsedTypeParameters(dt, udt.TypeArgs), udt.tok, w, true);
          w.Write(")");
          return w.ToString();
        } else if (xType.IsNonNullRefType) {
          // what we emit here will only be used to construct a dummy value that programmer-supplied code will overwrite later
          return "_dafny.Rtd_ref/*not used*/";
        } else {
          Contract.Assert(cl is NewtypeDecl || cl is SubsetTypeDecl);
          return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody, ConcreteSyntaxTree wr) {
      if (createBody) {
        wr.Write("{0}get {1}()", isStatic ? "static " : "", name);
        var w = wr.NewBlock("", ";");
        if (!isStatic) {
          w.WriteLine("let _this = this;");
        }
        return w;
      } else {
        return null;
      }
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree wr) {
      if (createBody) {
        wr.Write($"get {name}()");
        var wGet = wr.NewBlock("", ";");
        wGet.WriteLine("let _this = this;");

        wr.Write($"set {name}(value)");
        var wSet = wr.NewBlock("", ";");
        wSet.WriteLine("let _this = this;");

        setterWriter = wSet;
        return wGet;
      } else {
        setterWriter = null;
        return null;
      }
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      var block = wr.NewBlock("TAIL_CALL_START: while (true)");
      if (member is Method m) {
        var beforeReturnBlock = block.Fork(0);
        EmitReturn(m.Outs, block);
        return beforeReturnBlock;
      }
      return block;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    private static string CharFromNumberMethodName() {
      return UnicodeCharEnabled ? "new _dafny.CodePoint" : "String.fromCharCode";
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl /*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(type);
      if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "char";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigNumber";
      } else if (xType is RealType) {
        return "Dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigNumber";
      } else if (xType.AsNewtype != null && member == null) {  // when member is given, use UserDefinedType case below
        NativeType nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(xType.AsNewtype.BaseType, wr, tok);
      } else if (xType.IsObjectQ) {
        return "object";
      } else if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(xType);
        TypeName_SplitArrayName(elType, wr, tok, out var typeNameSansBrackets, out var brackets);
        return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets;
      } else if (xType is UserDefinedType udt) {
        var s = FullTypeName(udt, member);
        return TypeName_UDT(s, udt, wr, udt.tok);
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        return DafnySetClass;
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        return DafnySeqClass;
      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        return DafnyMultiSetClass;
      } else if (xType is MapType) {
        return DafnyMapClass;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      if (usePlaceboValue) {
        return "undefined";
      }

      var xType = type.NormalizeExpandKeepConstraints();

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return $"{CharFromNumberMethodName()}({CharType.DefaultValueAsString}.codePointAt(0))";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return IntegerLiteral(0);
      } else if (xType is RealType) {
        return "_dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : IntegerLiteral(0);
      } else if (xType is SetType) {
        return $"{DafnySetClass}.Empty";
      } else if (xType is MultiSetType) {
        return $"{DafnyMultiSetClass}.Empty";
      } else if (xType is SeqType seq) {
        if (seq.Arg.IsCharType) {
          return "''";
        }
        return $"{DafnySeqClass}.of()";
      } else if (xType is MapType) {
        return $"{DafnyMapClass}.Empty";
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter) {
        if (constructTypeParameterDefaultsFromTypeDescriptors) {
          return string.Format("{0}.Default", TypeDescriptor(udt, wr, udt.tok));
        } else {
          return FormatDefaultTypeParameterValue((TypeParameter)udt.ResolvedClass);
        }
      } else if (cl is OpaqueTypeDecl opaque) {
        return FormatDefaultTypeParameterValue(opaque);
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".Default";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return "null";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            if (arrayClass.Dims == 1) {
              return "[]";
            } else {
              return string.Format("_dafny.newArray(undefined, {0})", Util.Comma(arrayClass.Dims, _ => "_dafny.ZERO"));
            }
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return "null";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return "null";
        }
      } else if (cl is DatatypeDecl) {
        var dt = (DatatypeDecl)cl;
        var s = dt is TupleTypeDecl ? "_dafny.Tuple" : FullTypeName(udt);
        var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs).ConvertAll(ta => ta.Actual);
        return string.Format($"{s}.Default({Util.Comma(relevantTypeArgs, arg => DefaultValue(arg, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))})");
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      return s;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member) {
      // Companion classes in JavaScript are just the same as the type, except for erasable type wrappers
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
          DatatypeWrapperEraser.IsErasableDatatypeWrapper(dt, out _)) {
        var s = FullTypeName(udt, member);
        return TypeName_UDT(s, udt, wr, udt.tok);
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs, ConcreteSyntaxTree wr) {
      if (isStatic) {
        var w = wr.NewNamedBlock("static get {0}()", name);
        EmitReturnExpr(rhs, w);
      } else {
        wr.WriteLine("this.{0} = {1};", name, rhs);
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write("{0}{1}", prefix, name);
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, ConcreteSyntaxTree wr) {
      wr.Write("let {0}", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, ConcreteSyntaxTree wr) {
      wr.Write("let {0} = ", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, ConcreteSyntaxTree wr) {
      wr.Write("let {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, ConcreteSyntaxTree wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
      } else {
        for (var i = 0; i < actualOutParamNames.Count; i++) {
          wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, ConcreteSyntaxTree wr, IToken tok) {
      return "let " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      bool isString = arg.Type.IsStringType;
      bool isStringLiteral = arg is StringLiteralExpr;
      bool isGeneric = arg.Type.AsSeqType != null &&
                       arg.Type.AsSeqType.Arg.IsTypeParameter;
      var wStmts = wr.Fork();
      if (isStringLiteral && !UnicodeCharEnabled) {
        // process.stdout.write(_dafny.toString(x));
        wr.Write("process.stdout.write(_dafny.toString(");
        TrExpr(arg, wr, false, wStmts);
        wr.WriteLine("));");
      } else if (isString) {
        if (UnicodeCharEnabled) {
          wr.Write($"process.stdout.write(");
          TrParenExpr(arg, wr, false, wStmts);
          wr.WriteLine(".toVerbatimString(false));");
        } else {
          wr.Write($"process.stdout.write(_dafny.toString({DafnySeqClass}.JoinIfPossible(");
          TrExpr(arg, wr, false, wStmts);
          wr.WriteLine(")));");
        }
      } else if (isGeneric && !UnicodeCharEnabled) {
        // try { process.stdout.write(_dafny.toString(((x) instanceof Array && typeof((x)[0]) == \"string\") ? (x).join("") : (x))); } catch (_error) { process.stdout.write(_dafny.toString(x)); }
        wr.Write("try { process.stdout.write(_dafny.toString(");
        wr.Write("(");
        wr.Write("(");
        TrExpr(arg, wr, false, wStmts);
        wr.Write(") instanceof Array && typeof((");
        TrExpr(arg, wr, false, wStmts);
        wr.Write(")[0]) == \"string\") ? ");
        wr.Write("(");
        TrExpr(arg, wr, false, wStmts);
        wr.Write(").join(\"\")");
        wr.Write(":");
        wr.Write("(");
        TrExpr(arg, wr, false, wStmts);
        wr.Write(")));");
        wr.Write("} catch (_error) { process.stdout.write(_dafny.toString(");
        TrExpr(arg, wr, false, wStmts);
        wr.WriteLine("));}");
      } else { // !isString && !isGeneric
        // process.stdout.write(_dafny.toString(x));
        wr.Write("process.stdout.write(_dafny.toString(");
        TrExpr(arg, wr, false, wStmts);
        wr.WriteLine("));");
      }
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (outParams.Count == 0) {
        wr.WriteLine("return;");
      } else if (outParams.Count == 1) {
        wr.WriteLine("return {0};", IdName(outParams[0]));
      } else {
        wr.WriteLine("return [{0}];", Util.Comma(outParams, IdName));
      }
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var prefix = createContinueLabel ? "C" : "L";
      return wr.NewNamedBlock($"{prefix}{label}:");
    }

    protected override void EmitBreak(string/*?*/ label, ConcreteSyntaxTree wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("break L{0};", label);
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine("break C{0};", label);
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      wr.WriteLine("yield null;");
    }

    protected override void EmitAbsurd(string/*?*/ message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw new Error(\"{0}\");", message);
    }

    protected override void EmitHalt(IToken tok, Expression/*?*/ messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("throw new _dafny.HaltException(");
      if (tok != null) {
        wr.Write("\"" + Dafny.ErrorReporter.TokenToString(tok) + ": \" + ");
      }

      TrParenExpr(messageExpr, wr, false, wStmts);
      if (UnicodeCharEnabled && messageExpr.Type.IsStringType) {
        wr.Write(".toVerbatimString(false)");
      }
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {

      var nativeType = AsNativeType(loopIndex.Type);

      wr.Write($"for (let {loopIndex.CompileName} = ");
      var startWr = wr.Fork();
      wr.Write($"; ");

      ConcreteSyntaxTree bodyWr;
      if (goingUp) {
        if (endVarName == null) {
          wr.Write("true");
        } else if (nativeType == null) {
          wr.Write($"{loopIndex.CompileName}.isLessThan({endVarName})");
        } else {
          wr.Write($"{loopIndex.CompileName} < {endVarName}");
        }
        if (nativeType == null) {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName} = {loopIndex.CompileName}.plus(_dafny.ONE))");
        } else {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName}++)");
        }
      } else {
        if (endVarName == null) {
          wr.Write("true");
        } else if (nativeType == null) {
          wr.Write($"{endVarName}.isLessThan({loopIndex.CompileName})");
        } else {
          wr.Write($"{endVarName} < {loopIndex.CompileName}");
        }
        bodyWr = wr.NewBlock($"; )");
        if (nativeType == null) {
          bodyWr.WriteLine($"{loopIndex.CompileName} = {loopIndex.CompileName}.minus(_dafny.ONE);");
        } else {
          bodyWr.WriteLine($"{loopIndex.CompileName}--;");
        }
      }
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
      start = start ?? "0";
      return wr.NewNamedBlock("for (let {0} = {2}; {0} < {1}; {0}++)", indexVar, bound, start);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for (let {0} = new BigNumber({1}); ; {0} = {0}.multipliedBy(2))", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} = {0}.plus(1);", varName);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0} = {0}.minus(1);", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return string.Format("_dafny.Quantifier");
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write("for (const {0} of ", tmpVarName);
      collectionWriter = wr.Fork();
      var wwr = wr.NewBlock(")");
      return wwr;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      wr.WriteLine("{0}{1} = {2};", introduceBoundVar ? "let " : "", boundVarName, tmpVarName);
    }

    [CanBeNull]
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree preconditions) {
      string typeTest;
      if (boundVarType.IsRefType) {
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          typeTest = "true";
        } else if (boundVarType.IsTraitType) {
          typeTest = $"_dafny.InstanceOfTrait({tmpVarName}, {TypeName(boundVarType, preconditions, tok)})";
        } else {
          typeTest = $"{tmpVarName} instanceof {TypeName(boundVarType, preconditions, tok)}";
        }

        if (boundVarType.IsNonNullRefType) {
          typeTest = $"{tmpVarName} !== null && " + typeTest;
        } else {
          typeTest = $"{tmpVarName} === null || " + typeTest;
        }
      } else {
        typeTest = "true";
      }
      return typeTest == "true" ? null : typeTest;
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write("for (const {0} of ", boundVarName);
      collectionWriter = wr.Fork();
      return wr.NewBlock(")");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall /*?*/, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      if (cl.Name == "object") {
        wr.Write("_dafny.NewObject()");
      } else {
        wr.Write("new {0}(", TypeName(type, wr, tok));
        EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, wr);
        wr.Write(")");
      }
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var initValue = mustInitialize ? DefaultValue(elementType, wr, tok, true) : null;
      if (dimensions.Count == 1) {
        // handle the common case of 1-dimensional arrays separately
        wr.Write($"Array(({dimensions[0]}).toNumber())");
        if (initValue != null) {
          wr.Write(".fill({0})", initValue);
        }
      } else {
        // the general case
        wr.Write("_dafny.newArray({0}, {1})", initValue ?? "undefined", dimensions.Comma(s => s));
      }
    }

    protected string TranslateEscapes(string s) {
      s = Util.ReplaceNullEscapesWithCharacterEscapes(s);

      s = Util.UnicodeEscapesToLowercase(s);

      return s;
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("null");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var escaped = TranslateEscapes((string)e.Value);
        if (UnicodeCharEnabled) {
          wr.Write($"new _dafny.CodePoint('{escaped}'.codePointAt(0))");
        } else {
          wr.Write($"'{escaped}'");
        }
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        if (UnicodeCharEnabled) {
          wr.Write($"_dafny.Seq.UnicodeFromString(");
          TrStringLiteral(str, wr);
          wr.Write(")");
        } else {
          TrStringLiteral(str, wr);
        }
      } else if (AsNativeType(e.Type) != null) {
        wr.Write(e.Value.ToString());
      } else if (e.Value is BigInteger) {
        var i = (BigInteger)e.Value;
        wr.Write(IntegerLiteral(i));
      } else if (e.Value is BaseTypes.BigDec) {
        var n = (BaseTypes.BigDec)e.Value;
        if (0 <= n.Exponent) {
          wr.Write("new _dafny.BigRational(new BigNumber(\"{0}", n.Mantissa);
          for (int i = 0; i < n.Exponent; i++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        } else {
          wr.Write($"new _dafny.BigRational({IntegerLiteral(n.Mantissa)}, new BigNumber(\"1");
          for (int i = n.Exponent; i < 0; i++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
    string IntegerLiteral(BigInteger i) {
      if (i.IsZero) {
        return "_dafny.ZERO";
      } else if (i.IsOne) {
        return "_dafny.ONE";
      } else if (-0x20_0000_0000_0000L < i && i < 0x20_0000_0000_0000L) {  // 53 bits, plus sign
        return $"new BigNumber({i})";
      } else {
        return $"new BigNumber(\"{i}\")";
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      var n = str.Length;
      if (!isVerbatim) {
        wr.Write($"\"{TranslateEscapes(str)}\"");
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

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      if (bvType.NativeType == null) {
        wr.Write("(");
        var middle = wr.Fork();
        wr.Write(").mod(new BigNumber(2).exponentiatedBy({0}))", bvType.Width);
        return middle;
      } else if (bvType.NativeType.Bitwidth != bvType.Width) {
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
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      var bv = e0.Type.AsBitVectorType;
      if (bv.Width == 0) {
        tr(e0, wr, inLetExprBody, wStmts);
      } else {
        wr.Write("_dafny.{0}(", isRotateLeft ? "RotateLeft" : "RotateRight");
        tr(e0, wr, inLetExprBody, wStmts);
        wr.Write(", (");
        tr(e1, wr, inLetExprBody, wStmts);
        wr.Write(").toNumber(), {0})", bv.Width);
        if (needsCast) {
          wr.Write(".toNumber()");
        }
      }
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("[]", tupleTypeArgs);
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write("{0}.push(_dafny.Tuple.of(", ingredients, tupleTypeArgs);
      var wrTuple = wr.Fork();
      wr.WriteLine("));");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write("{0}[{1}]", prefix, i);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      switch (name) {
        case "arguments":
        case "await":
        case "boolean":
        case "byte":
        case "catch":
        case "continue":
        case "debugger":
        case "default":
        case "delete":
        case "do":
        case "double":
        case "enum":
        case "eval":
        case "final":
        case "finally":
        case "float":
        case "for":
        case "goto":
        case "implements":
        case "instanceof":
        case "interface":
        case "let":
        case "long":
        case "native":
        case "package":
        case "private":
        case "public":
        case "short":
        case "super":
        case "switch":
        case "synchronized":
        case "throw":
        case "throws":
        case "transient":
        case "try":
        case "typeof":
        case "void":
        case "volatile":
        case "with":
        case "toString":
        case "equals":
          return "_$$_" + name;
        default:
          return name;
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.CompileName);
      } else if (cl is ClassDecl cdecl && cdecl.IsDefaultClass && Attributes.Contains(cl.EnclosingModuleDefinition.Attributes, "extern") &&
        member != null && Attributes.Contains(member.Attributes, "extern")) {
        // omit the default class name ("_default") in extern modules, when the class is used to qualify an extern member
        Contract.Assert(!cl.EnclosingModuleDefinition.IsDefaultModule);  // default module is not marked ":extern"
        return IdProtect(cl.EnclosingModuleDefinition.CompileName);
      } else {
        return IdProtect(cl.EnclosingModuleDefinition.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      wr.Write("_this");
    }

    protected override ConcreteSyntaxTree EmitCast(Type toType, ConcreteSyntaxTree wr) {
      return wr;
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, ConcreteSyntaxTree wr) {
      var dtName = dt.FullCompileName;
      var ctorName = ctor.CompileName;

      if (dt is TupleTypeDecl) {
        wr.Write("_dafny.Tuple.of({0})", arguments);
      } else if (!isCoCall) {
        // Ordinary constructor (that is, one that does not guard any co-recursive calls)
        // Generate: Dt.create_Ctor(arguments)
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
          if (idParam == null) {
            compiledName = "length";
          } else {
            compiledName = "dims[" + (int)idParam + "]";
          }
          if (id == SpecialField.ID.ArrayLength) {
            preString = "new BigNumber(";
            postString = ")";
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

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string/*?*/ additionalCustomParameter, bool internalAccess = false) {
      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(member);
      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        return SimpleLvalue(obj);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return SimpleLvalue(w => w.Write("true"));
      } else if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl) {
        Contract.Assert(dtor.CorrespondingFormals.Count == 1);
        var formal = dtor.CorrespondingFormals[0];
        return SuffixLvalue(obj, "[{0}]", formal.NameForCompilation);
      } else if (member is SpecialField sf && !(member is ConstantField)) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out compiledName, out preStr, out postStr);
        if (compiledName.Length != 0) {
          return SuffixLvalue(obj, ".{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
          return SimpleLvalue(obj);
        }
      } else if (member is Function fn) {
        typeArgs = typeArgs.Where(ta => NeedsTypeDescriptor(ta.Formal)).ToList();
        if (typeArgs.Count == 0 && additionalCustomParameter == null) {
          if (member.IsStatic) {
            return SuffixLvalue(obj, ".{0}", IdName(member));
          } else {
            // generate: obj.F.bind(obj)
            return SimpleLvalue(w => {
              var objWriter = new ConcreteSyntaxTree();
              obj(objWriter);
              var objString = objWriter.ToString();
              w.Write("{0}.{1}.bind({0})", objString, IdName(member));
            });
          }
        } else {
          // We need an eta conversion to adjust for the difference in arity.
          // (T0 a0, T1 a1, ...) -> obj.F(rtd0, rtd1, ..., additionalCustomParameter, a0, a1, ...)
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
          prefixWr.Write("(");
          foreach (var arg in fn.Formals) {
            if (!arg.IsGhost) {
              var name = idGenerator.FreshId("_eta");
              prefixWr.Write("{0}{1}", prefixSep, name);
              suffixWr.Write("{0}{1}", suffixSep, name);
              suffixSep = ", ";
              prefixSep = ", ";
            }
          }
          prefixWr.Write(") => ");
          suffixWr.Write(")");
          return EnclosedLvalue(prefixWr.ToString(), obj, $".{suffixWr.ToString()}");
        }
      } else {
        Contract.Assert(member is Field);
        if (member.IsStatic) {
          return SimpleLvalue(w => {
            w.Write("{0}.{1}", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            var sep = "(";
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w, ref sep);
            if (sep != "(") {
              w.Write(")");
            }
          });
        } else if (NeedsCustomReceiver(member) && !(member.EnclosingClass is TraitDecl)) {
          // instance const in a newtype
          return SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            obj(w);
            w.Write(")");
          });
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          return SuffixLvalue(obj, $"._{member.CompileName}");
        } else {
          return SimpleLvalue(w => {
            obj(w);
            w.Write(".{0}", IdName(member));
            var sep = "(";
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w, ref sep);
            if (sep != "(") {
              w.Write(")");
            }
          });
        }
      }
    }

    protected override ConcreteSyntaxTree ExprToInt(Type fromType, ConcreteSyntaxTree wr) {
      if (AsNativeType(fromType) == null) {
        return wr;
      }
      wr.Write("BigNumber");
      return wr.ForkInParens();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write("[{0}]", indices[0]);
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[{0}]", index);
        }
      }
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write("[");
        TrExpr(indices[0], wr, inLetExprBody, wStmts);
        wr.Write("]");
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[");
          TrExpr(index, wr, inLetExprBody, wStmts);
          wr.Write("]");
        }
      }
      return w;
    }

    protected override string ArrayIndexToInt(string arrayIndex) => $"new BigNumber({arrayIndex})";

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(expr, wr, inLetExprBody, wStmts);
      if (AsNativeType(expr.Type) == null) {
        wr.Write(".toNumber()");
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      if (source.Type.NormalizeExpand() is SeqType) {
        // seq
        wr.Write("[");
        TrExpr(index, wr, inLetExprBody, wStmts);
        wr.Write("]");
      } else {
        // map or imap
        wr.Write(".get(");
        TrExpr(index, wr, inLetExprBody, wStmts);
        wr.Write(")");
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (source.Type.AsSeqType != null) {
        wr.Write($"{DafnySeqClass}.update(");
        TrExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(", ");
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".update(");
      }
      TrExpr(index, wr, inLetExprBody, wStmts);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody, wStmts);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
        bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (fromArray) {
        wr.Write($"{DafnySeqClass}.of(...");
      }
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      if (lo != null) {
        wr.Write(".slice(");
        TrExpr(lo, wr, inLetExprBody, wStmts);
        if (hi != null) {
          wr.Write(", ");
          TrExpr(hi, wr, inLetExprBody, wStmts);
        }
        wr.Write(")");
      } else if (hi != null) {
        wr.Write(".slice(0, ");
        TrExpr(hi, wr, inLetExprBody, wStmts);
        wr.Write(")");
      } else if (fromArray) {
        wr.Write(".slice()");
      }
      if (fromArray) {
        wr.Write(")");
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var fromType = (ArrowType)expr.Initializer.Type.NormalizeExpand();
      wr.Write($"{DafnySeqClass}.Create(");
      TrExpr(expr.N, wr, inLetExprBody, wStmts);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody, wStmts);
      wr.Write(")");
      if (fromType.Result.IsCharType && !UnicodeCharEnabled) {
        wr.Write(".join('')");
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr($"{DafnyMultiSetClass}.FromArray", expr.E, wr, inLetExprBody, wStmts);
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      wr.Write("(({0}) => ", Util.Comma(boundVars));
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return w;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
        wr.Write(source);
      } else if (ctor.EnclosingDatatype is TupleTypeDecl tupleTypeDecl) {
        Contract.Assert(tupleTypeDecl.NonGhostDims != 1); // such a tuple is an erasable-wrapper type, handled above
        wr.Write("({0})[{1}]", source, formalNonGhostIndex);
      } else {
        var dtorName = FormalName(dtor, formalNonGhostIndex);
        wr.Write("({0}){1}.{2}", source, ctor.EnclosingDatatype is CoDatatypeDecl ? "._D()" : "", dtorName);
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      wr.Write("function (");
      Contract.Assert(inTypes.Count == inNames.Count);  // guaranteed by precondition
      for (var i = 0; i < inNames.Count; i++) {
        wr.Write("{0}{1}", i == 0 ? "" : ", ", inNames[i]);
      }
      var w = wr.NewExprBlock(")");
      return w;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      var w = wr.NewExprBlock("function ({0})", bvName);
      wStmts = w.Fork();
      w.Write("return ");
      wrBody = w.Fork();
      w.WriteLine(";");
      wr.Write("(");
      wrRhs = wr.Fork();
      wr.Write(")");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var w = wr.NewBigExprBlock("function ()", "()");
      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var w = wr.NewExprBlock("function ({0})", bvName);
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
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(expr.Type.AsBitVectorType.Width == 0);
            wr.Write("0");
          } else {
            wr.Write("_dafny.BitwiseNot(");
            TrExpr(expr, wr, inLetExprBody, wStmts);
            wr.Write(", {0})", expr.Type.AsBitVectorType.Width);
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr("new BigNumber(", expr, wr, inLetExprBody, wStmts);
          if (expr.Type.AsMultiSetType != null) {
            wr.Write(".cardinality())");
          } else {
            wr.Write(".length)");
          }
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || (t.IsCharType && !UnicodeCharEnabled) || AsNativeType(t) != null || t.IsRefType;
    }

    bool IsRepresentedAsBigNumber(Type t) {
      if (AsNativeType(t) != null) {
        return false;
      } else if (t.AsBitVectorType is { } bvt) {
        return bvt.NativeType == null;
      } else {
        return t.IsNumericBased(Type.NumericPersuasion.Int)
          || t.IsBitVectorType
          || t.IsBigOrdinalType;
      }
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
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "==="; break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          if (AsNativeType(resultType) != null) {
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(resultType.AsBitVectorType.Width < 32);
            opString = "&";
          } else {
            staticCallString = "_dafny.BitwiseAnd";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          if (AsNativeType(resultType) != null) {
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(resultType.AsBitVectorType.Width < 32);
            opString = "|";
          } else {
            staticCallString = "_dafny.BitwiseOr";
          }
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          if (AsNativeType(resultType) != null) {
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(resultType.AsBitVectorType.Width < 32);
            opString = "^";
          } else {
            staticCallString = "_dafny.BitwiseXor";
          }
          break;

        case BinaryExpr.ResolvedOpcode.EqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "===";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "===";
            } else if (eqType.IsIntegerType || eqType.IsBitVectorType) {
              callString = "isEqualTo";
            } else if (eqType.IsRealType) {
              callString = "equals";
            } else {
              staticCallString = "_dafny.areEqual";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!==";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "!==";
            } else if (eqType.IsIntegerType) {
              preOpString = "!";
              callString = "isEqualTo";
            } else if (eqType.IsRealType) {
              preOpString = "!";
              callString = "equals";
            } else {
              preOpString = "!";
              staticCallString = "_dafny.areEqual";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
          if (AsNativeType(e0.Type) != null) {
            opString = "<";
          } else if (IsRepresentedAsBigNumber(e0.Type) || e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            callString = "isLessThan";
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
          break;
        case BinaryExpr.ResolvedOpcode.Le:
          if (AsNativeType(e0.Type) != null) {
            opString = "<=";
          } else if (IsRepresentedAsBigNumber(e0.Type)) {
            callString = "isLessThanOrEqualTo";
          } else if (e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            callString = "isAtMost";
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
          if (AsNativeType(e0.Type) != null) {
            opString = ">=";
          } else if (IsRepresentedAsBigNumber(e0.Type)) {
            callString = "isLessThanOrEqualTo";
            reverseArguments = true;
          } else if (e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            callString = "isAtMost";
            reverseArguments = true;
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          if (AsNativeType(e0.Type) != null) {
            opString = ">";
          } else if (IsRepresentedAsBigNumber(e0.Type) || e0.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            callString = "isLessThan";
            reverseArguments = true;
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }
          break;
        case BinaryExpr.ResolvedOpcode.LtChar when UnicodeCharEnabled:
          callString = "isLessThan";
          break;
        case BinaryExpr.ResolvedOpcode.LeChar when UnicodeCharEnabled:
          callString = "isLessThanOrEqual";
          break;
        case BinaryExpr.ResolvedOpcode.GtChar when UnicodeCharEnabled:
          callString = "isLessThan";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.GeChar when UnicodeCharEnabled:
          callString = "isLessThanOrEqual";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          if (AsNativeType(resultType) != null) {
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(resultType.AsBitVectorType.Width == 0);
            opString = "+";  // 0 + 0 == 0 == 0 << 0
            convertE1_to_int = true;
          } else {
            staticCallString = "_dafny.ShiftLeft";
            truncateResult = true; convertE1_to_int = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          if (AsNativeType(resultType) != null) {
            // JavaScript bitwise operators are weird (numeric operands are first converted into
            // signed 32-bit values), and it could be easy to forget how weird they are.
            // Therefore, as a protective measure, the following assert is here to catch against any future
            // change that would render this translation incorrect.
            Contract.Assert(resultType.AsBitVectorType.Width == 0);
            opString = "+";  // 0 + 0 == 0 == 0 << 0
            convertE1_to_int = true;
          } else {
            staticCallString = "_dafny.ShiftRight";
            truncateResult = true; convertE1_to_int = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          if (resultType.IsIntegerType || resultType.IsRealType || resultType.IsBigOrdinalType) {
            callString = "plus"; truncateResult = true;
          } else if (AsNativeType(resultType) != null) {
            opString = "+";
          } else if (resultType.IsCharType) {
            staticCallString = $"_dafny.{CharMethodQualifier}PlusChar";
          } else {
            callString = "plus"; truncateResult = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.IsIntegerType || resultType.IsRealType || resultType.IsBigOrdinalType) {
            callString = "minus"; truncateResult = true;
          } else if (AsNativeType(resultType) != null) {
            opString = "-";
          } else if (resultType.IsCharType) {
            staticCallString = $"_dafny.{CharMethodQualifier}MinusChar";
          } else {
            callString = "minus"; truncateResult = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          if (resultType.IsIntegerType || resultType.IsRealType) {
            callString = "multipliedBy"; truncateResult = true;
          } else if (AsNativeType(resultType) != null) {
            opString = "*";
          } else {
            callString = "multipliedBy"; truncateResult = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsRealType) {
            callString = "dividedBy";
          } else if (resultType.IsIntegerType || AsNativeType(resultType) == null) {
            staticCallString = "_dafny.EuclideanDivision";
          } else if (AsNativeType(resultType).LowerBound < BigInteger.Zero) {
            staticCallString = "_dafny.EuclideanDivisionNumber";
          } else {
            opString = "/";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType) {
            callString = "mod";
          } else if (AsNativeType(resultType) == null) {
            callString = "mod";
          } else if (AsNativeType(resultType).LowerBound < BigInteger.Zero) {
            staticCallString = "_dafny.EuclideanModuloNumber";
          } else {
            opString = "%";
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "equals"; break;
        case BinaryExpr.ResolvedOpcode.SeqEq:
          // a sequence may be represented as an array or as a string
          staticCallString = "_dafny.areEqual"; break;

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
          callString = "contains"; reverseArguments = true; break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "Union"; break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          callString = "Merge"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "Intersect"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "Difference"; break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          callString = "Subtract"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          staticCallString = $"{DafnySeqClass}.IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          staticCallString = $"{DafnySeqClass}.IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = $"{DafnySeqClass}.Concat"; break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          staticCallString = $"{DafnySeqClass}.contains"; reverseArguments = true; break;

        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments, out truncateResult, out convertE1_to_int,
            errorWr);
          break;
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write("{0}.isZero()", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType || e.E.Type.IsBigOrdinalType) {
        if (e.ToType.Equals(e.E.Type)) {
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
        } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("new _dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null || e.E.Type.IsCharType) {
            wr.Write("new BigNumber");
          }
          if (e.E.Type.IsCharType) {
            wr.Write("(");
          }

          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          if (e.E.Type.IsCharType) {
            wr.Write(UnicodeCharEnabled ? ".value)" : ".charCodeAt(0))");
          }

          wr.Write(", new BigNumber(1))");
        } else if (e.ToType.IsCharType) {
          wr.Write($"{CharFromNumberMethodName()}(");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          if (AsNativeType(e.E.Type) == null) {
            wr.Write(".toNumber()");
          }
          wr.Write(")");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative != null && toNative != null) {
            // from a native, to a native -- simple!
            TrExpr(e.E, wr, inLetExprBody, wStmts);
          } else if (e.E.Type.IsCharType) {
            Contract.Assert(fromNative == null);
            if (toNative == null) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("new BigNumber(");
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
              wr.Write(UnicodeCharEnabled ? ".value)" : ".charCodeAt(0))");
            } else {
              // char -> native
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
              wr.Write(UnicodeCharEnabled ? ".value" : ".charCodeAt(0)");
            }
          } else if (fromNative == null && toNative == null) {
            // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
            TrExpr(e.E, wr, inLetExprBody, wStmts);
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("new BigNumber");
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          } else {
            // any (int or bv) -> native (int or bv)
            // Consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("(" + literal + ")");
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              TrParenExpr(u.E, wr, inLetExprBody, wStmts);
              wr.Write(".length");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              TrParenExpr(m.Obj, wr, inLetExprBody, wStmts);
              wr.Write(".length");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody, wStmts);
              wr.Write(".toNumber()");
            }
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody, wStmts);
        } else if (e.ToType.IsCharType) {
          wr.Write($"{CharFromNumberMethodName()}(");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".toBigNumber().toNumber())");
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".toBigNumber()");
          if (AsNativeType(e.ToType) != null) {
            wr.Write(".toNumber()");
          }
        }
      } else if (e.E.Type.IsBigOrdinalType) {
        if (e.ToType.IsCharType) {
          wr.Write($"{CharFromNumberMethodName()}((");
        }

        TrExpr(e.E, wr, inLetExprBody, wStmts);
        if (e.ToType.IsCharType) {
          wr.Write(").toNumber())");
        }
      } else {
        Contract.Assert(false, $"not implemented for javascript: {e.E.Type} -> {e.ToType}");
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      Contract.Requires(fromType.IsRefType);
      Contract.Requires(toType.IsRefType);

      if (!fromType.IsNonNullRefType) {
        if (toType.IsNonNullRefType) {
          wr.Write($"{localName} != null && ");
        } else {
          wr.Write($"{localName} == null || (");
        }
      }

      if (toType.IsObject || toType.IsObjectQ) {
        wr.Write("true");
      } else if (toType.IsTraitType) {
        wr.Write($"_dafny.InstanceOfTrait({localName}, {TypeName(toType, wr, tok)})");
      } else {
        wr.Write($"{localName} instanceof {TypeName(toType, wr, tok)}");
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

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (ct is SetType) {
        wr.Write($"{DafnySetClass}.fromElements");
        TrExprList(elements, wr, inLetExprBody, wStmts);
      } else if (ct is MultiSetType) {
        wr.Write($"{DafnyMultiSetClass}.fromElements");
        TrExprList(elements, wr, inLetExprBody, wStmts);
      } else {
        Contract.Assert(ct is SeqType);  // follows from precondition
        ConcreteSyntaxTree wrElements;
        if (ct.Arg.IsCharType && !UnicodeCharEnabled) {
          // We're really constructing a string.
          // TODO: It may be that ct.Arg is a type parameter that may stand for char. We currently don't catch that case here.
          wr.Write("[");
          wrElements = wr.Fork();
          wr.Write("].join(\"\")");
        } else {
          wr.Write($"{DafnySeqClass}.of(");
          wrElements = wr.Fork();
          wr.Write(")");
        }
        string sep = "";
        foreach (var e in elements) {
          wrElements.Write(sep);
          TrExpr(e, wrElements, inLetExprBody, wStmts);
          sep = ", ";
        }
      }
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyMapClass}.of(");
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("[");
        TrExpr(p.A, wr, inLetExprBody, wStmts);
        wr.Write(",");
        TrExpr(p.B, wr, inLetExprBody, wStmts);
        wr.Write("]");
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write($"new {DafnySetClass}()");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write($"new {DafnyMapClass}()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      Contract.Assume(ct is SetType || ct is MultiSetType);  // follows from precondition
      var wStmts = wr.Fork();
      wr.Write("{0}.add(", collName);
      TrExpr(elmt, wr, inLetExprBody, wStmts);
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("{0}.push([", collName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody, wStmts);
      wr.WriteLine("]);");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      // collections are built in place
      return collName;
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr("_dafny.SingleValue", e, wr, inLetExprBody, wStmts);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var tryBlock = wr.NewBlock("try");
      TrStmt(body, tryBlock);
      var catchBlock = wr.NewBlock("catch (e)");
      var ifBlock = catchBlock.NewBlock("if (e instanceof _dafny.HaltException)");
      ifBlock.WriteLine($"let {haltMessageVarName} = e.message;");
      TrStmt(recoveryBody, ifBlock);
      var elseBlock = catchBlock.NewBlock("else");
      elseBlock.WriteLine("throw e");
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (runAfterCompile) {
        Contract.Assert(callToMain != null);  // this is part of the contract of CompileTargetProgram
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'node'
        // will run the program.
        return true;
      } else {
        // compile now
        return SendToNewNodeProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames, outputWriter);
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      return SendToNewNodeProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames, outputWriter);
    }

    public string ToStringLiteral(string s) {
      var wr = new ConcreteSyntaxTree();
      EmitStringLiteral(s, false, wr);
      return wr.ToString();
    }

    bool SendToNewNodeProcess(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      TextWriter outputWriter) {
      Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

      var psi = new ProcessStartInfo("node", "") {
        RedirectStandardInput = true,
        StandardInputEncoding = Encoding.UTF8,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
      };

      try {
        Process nodeProcess = Process.Start(psi);
        foreach (var filename in otherFileNames) {
          WriteFromFile(filename, nodeProcess.StandardInput);
        }
        nodeProcess.StandardInput.Write(targetProgramText);
        if (callToMain != null && DafnyOptions.O.RunAfterCompile) {
          nodeProcess.StandardInput.WriteLine("require('process').stdout.setEncoding(\"utf-8\");");
          nodeProcess.StandardInput.WriteLine("require('process').argv = [\"node\",\"stdin\", " + string.Join(",", DafnyOptions.O.MainArgs.Select(ToStringLiteral)) + "];");
          nodeProcess.StandardInput.Write(callToMain);
        }
        nodeProcess.StandardInput.Flush();
        nodeProcess.StandardInput.Close();
        // Fixes a problem of Node on Windows, where Node does not prints to the parent console its standard outputs.
        var errorProcessing = Task.Run(() => {
          PassthroughBuffer(nodeProcess.StandardError, Console.Error);
        });
        PassthroughBuffer(nodeProcess.StandardOutput, Console.Out);
        nodeProcess.WaitForExit();
        errorProcessing.Wait();
        return nodeProcess.ExitCode == 0;
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start node.js ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }

    // We read character by character because we did not find a way to ensure
    // final newlines are kept when reading line by line
    private static void PassthroughBuffer(TextReader input, TextWriter output) {
      int current;
      while ((current = input.Read()) != -1) {
        output.Write((char)current);
      }
    }
  }
}
