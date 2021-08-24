//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
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
using System.Reflection;
using System.Collections.ObjectModel;
using Bpl = Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis;
using System.Runtime.Loader;
using System.Text.Json;
using Microsoft.BaseTypes;
using static Microsoft.Dafny.ConcreteSyntaxTreeUtils;
  
namespace Microsoft.Dafny
{
  public class CsharpCompiler : Compiler
  {
    public CsharpCompiler(ErrorReporter reporter)
      : base(reporter) {
    }

    public override string TargetLanguage => "C#";

    const string DafnyISet = "Dafny.ISet";
    const string DafnyIMultiset = "Dafny.IMultiSet";
    const string DafnyISeq = "Dafny.ISequence";
    const string DafnyIMap = "Dafny.IMap";

    const string DafnySetClass = "Dafny.Set";
    const string DafnyMultiSetClass = "Dafny.MultiSet";
    const string DafnySeqClass = "Dafny.Sequence";
    const string DafnyMapClass = "Dafny.Map";

    const string DafnyHelpersClass = "Dafny.Helpers";

    static string FormatTypeDescriptorVariable(string typeVarName) => $"_td_{typeVarName}";
    static string FormatTypeDescriptorVariable(TypeParameter tp) => FormatTypeDescriptorVariable(tp.CompileName);
    const string TypeDescriptorMethodName = "_TypeDescriptor";

    static string FormatDefaultTypeParameterValue(TopLevelDecl tp) {
      Contract.Requires(tp is TypeParameter || tp is OpaqueTypeDecl);
      if (tp is OpaqueTypeDecl) {
        // This is unusual. Typically, the compiler never needs to compile an opaque type, but this opaque type
        // is apparently an :extern (or a compiler error has already been reported and we're just trying to get to
        // the end of compilation without crashing). It's difficult to say what the compiler could do in this situation, since
        // it doesn't know how to generate code that produces a legal value of the opaque type. If we don't do
        // anything different from the common case (the "else" branch below), then the code emitted will not
        // compile (see github issue #1151). So, to do something a wee bit better, we emit a placebo value. This
        // will only work when the opaque type is in the same module and has no type parameters.
        return $"default({tp.EnclosingModuleDefinition.CompileName + "." + tp.CompileName})";
      } else {
        // this is the common case
        return $"_default_{tp.CompileName}";
      }
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine("// To recompile, you will need the libraries");
      wr.WriteLine("//     System.Runtime.Numerics.dll System.Collections.Immutable.dll");
      wr.WriteLine("// but the 'dotnet' tool in net5.0 should pick those up automatically.");
      wr.WriteLine("// Optionally, you may want to include compiler switches like");
      wr.WriteLine("//     /debug /nowarn:162,164,168,183,219,436,1717,1718");
      wr.WriteLine();
      wr.WriteLine("using System;");
      wr.WriteLine("using System.Numerics;");
      EmitDafnySourceAttribute(program, wr);
      if (!DafnyOptions.O.UseRuntimeLib) {
        ReadRuntimeSystem("DafnyRuntime.cs", wr);
      }
    }

    void EmitDafnySourceAttribute(Program program, ConcreteSyntaxTree wr) {
      Contract.Requires(program != null);
      Contract.Requires(wr != null);

      var strwr = new StringWriter();
      strwr.NewLine = Environment.NewLine;
      new Printer(strwr, DafnyOptions.PrintModes.DllEmbed).PrintProgram(program, true);
      var programString = strwr.GetStringBuilder().Replace("\"", "\"\"").ToString();

      wr.WriteLine($"[assembly: DafnyAssembly.DafnySourceAttribute(@\"{programString}\")]");
      wr.WriteLine();
    }

    protected override void EmitBuiltInDecls(BuiltIns builtIns, ConcreteSyntaxTree wr) {
      var dafnyNamespace = CreateModule("Dafny", false, false, null, wr);
      var arrayHelpers = dafnyNamespace.NewNamedBlock("internal class ArrayHelpers");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl classDecl) {
          int dims = classDecl.Dims;

          // Here is an overloading of the method name, where there is an initialValue parameter
          // public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
          arrayHelpers.Write($"public static T[{Repeat("", dims, ",")}] InitNewArray{dims}<T>(T z, {Repeat("BigInteger size{0}", dims, ", ")})");

          var w = arrayHelpers.NewBlock();
          // int s0 = (int)size0;
          for (int i = 0; i < dims; i++) {
            w.WriteLine("int s{0} = (int)size{0};", i);
          }

          // T[,] a = new T[s0, s1];
          w.WriteLine($"T[{Repeat("", dims, ",")}] a = new T[{Repeat("s{0}", dims, ",")}];");

          // for (int i0 = 0; i0 < s0; i0++) {
          //   for (int i1 = 0; i1 < s1; i1++) {
          var wLoopNest = w;
          for (int i = 0; i < dims; i++) {
            wLoopNest = wLoopNest.NewNamedBlock("for (int i{0} = 0; i{0} < s{0}; i{0}++)", i);
          }

          // a[i0,i1] = z;
          wLoopNest.WriteLine($"a[{Repeat("i{0}", dims, ",")}] = z;");
          // return a;
          w.WriteLine("return a;");
        }
      }
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw) {
      var wr = ((ClassWriter) cw).StaticMemberWriter;
      // See EmitCallToMain() - this is named differently because otherwise C# tries
      // to resolve the reference to the instance-level Main method
      return wr.NewBlock("public static void _StaticMain()");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, ConcreteSyntaxTree wr) {
      return wr.NewBlock($"namespace {IdProtect(moduleName)}", " // end of " + $"namespace {IdProtect(moduleName)}");
    }

    protected override string GetHelperModuleName() => DafnyHelpersClass;

    const string DafnyTypeDescriptor = "Dafny.TypeDescriptor";

    string TypeParameters(List<TypeParameter>/*?*/ targs) {
      Contract.Requires(targs == null || cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      if (targs == null || targs.Count == 0) {
        return "";
      }

      return $"<{targs.Comma(IdName)}>";
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      var wBody = WriteTypeHeader("partial class", name, typeParameters, superClasses, tok, wr);
      
      ConcreteSyntaxTree/*?*/ wCtorBody = null;
      if (cls is ClassDecl cl && !(cl is TraitDecl) && !cl.IsDefaultClass) {
        if (cl.Members.TrueForAll(member => !(member is Constructor ctor) || !ctor.IsExtern(out var _, out var _))) {
          // This is a (non-default) class with no :extern constructor, so emit a C# constructor for the target class
          var wTypeFields = wBody.Fork();

          var wCtorParams = new ConcreteSyntaxTree();
          wCtorBody = wBody.Format($"public {name}({wCtorParams})").NewBlock();

          if (typeParameters != null) {
            var sep = "";
            foreach (var ta in TypeArgumentInstantiation.ListFromFormals(typeParameters)) {
              if (NeedsTypeDescriptor(ta.Formal)) {
                var fieldName = FormatTypeDescriptorVariable(ta.Formal.CompileName);
                var decl = $"{DafnyTypeDescriptor}<{TypeName(ta.Actual, wTypeFields, ta.Formal.tok)}> {fieldName}";
                wTypeFields.WriteLine($"private {decl};");
                if (ta.Formal.Parent == cls) {
                  wCtorParams.Write($"{sep}{decl}");
                }

                wCtorBody.WriteLine($"this.{fieldName} = {TypeDescriptor(ta.Actual, wCtorBody, ta.Formal.tok)};");
                sep = ", ";
              }
            }
          }
        }
      }

      return new ClassWriter(this, wBody, wCtorBody);
    }

    /// <summary>
    /// Generate the "_TypeDescriptor" method for a generated class.
    /// </summary>
    private void EmitTypeDescriptorMethod(TopLevelDecl enclosingTypeDecl, ConcreteSyntaxTree wr) {
      Contract.Requires(enclosingTypeDecl != null);
      Contract.Requires(wr != null);

      var type = UserDefinedType.FromTopLevelDecl(enclosingTypeDecl.tok, enclosingTypeDecl);
      var initializer = TypeInitializationValue(type, wr, enclosingTypeDecl.tok, false, true);

      var targetTypeName = TypeName(type, wr, enclosingTypeDecl.tok);
      var typeDescriptorExpr = $"new {DafnyTypeDescriptor}<{targetTypeName}>({initializer})";

      if (enclosingTypeDecl.TypeArgs.Count == 0) {
        wr.WriteLine($"private static readonly {DafnyTypeDescriptor}<{targetTypeName}> _TYPE = {typeDescriptorExpr};");
        typeDescriptorExpr = "_TYPE"; // use the precomputed value
      }

      List<TypeParameter> typeDescriptorParams;
      if (enclosingTypeDecl is DatatypeDecl dtDecl) {
        typeDescriptorParams = UsedTypeParameters(dtDecl);
      } else {
        typeDescriptorParams = enclosingTypeDecl.TypeArgs.Where(NeedsTypeDescriptor).ToList();
      }

      var parameters = typeDescriptorParams.Comma(tp => $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp.CompileName)}");
      var wTypeMethodBody = wr.Write($"public static {DafnyTypeDescriptor}<{targetTypeName}> {TypeDescriptorMethodName}({parameters})").NewBlock();
      wTypeMethodBody.WriteLine($"return {typeDescriptorExpr};");
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      var instanceMemberWriter = WriteTypeHeader("interface", name, typeParameters, superClasses, tok, wr);

      //writing the _Companion class
      wr.Write($"public class _Companion_{name}{TypeParameters(typeParameters)}");
      var staticMemberWriter = wr.NewBlock();

      return new ClassWriter(this, instanceMemberWriter, null, staticMemberWriter);
    }

    private ConcreteSyntaxTree WriteTypeHeader(string kind, string name, List<TypeParameter> typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      wr.Write($"public {kind} {IdProtect(name)}{TypeParameters(typeParameters)}");
      var realSuperClasses = superClasses?.Where(trait => !trait.IsObject).ToList() ?? new List<Type>();
      if (realSuperClasses.Any()) {
        wr.Write($" : {realSuperClasses.Comma(trait => TypeName(trait, wr, tok))}");
      }
      return wr.NewBlock();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      // An iterator is compiled as follows:
      //   public class MyIteratorExample<T>
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
      //     public bool MoveNext() {
      //       return _iter.MoveNext();
      //     }
      //
      //     private IEnumerator<object> TheIterator() {
      //       // the translation of the body of the iterator, with each "yield" turning into a "yield return null;"
      //       yield break;
      //     }
      //   }

      var cw = (ClassWriter) CreateClass(IdProtect(iter.EnclosingModuleDefinition.CompileName), IdName(iter), iter, wr);
      var w = cw.InstanceMemberWriter;
      // here come the fields

      var constructors = iter.Members.OfType<Constructor>().ToList();

      // we're expecting just one constructor 
      var enumerable = constructors.ToList();
      Contract.Assert(enumerable.Count == 1);
      Constructor ct = constructors[0];

      foreach (var member in iter.Members) {
        if (member is Field f && !f.IsGhost) {
          cw.DeclareField(IdName(f), iter, false, false, f.Type, f.tok, DefaultValue(f.Type, w, f.tok, true), f);
        }
      }

      w.WriteLine("System.Collections.Generic.IEnumerator<object> _iter;");

      // here we rely on the parameters and the corresponding fields having the same names
      var nonGhostFormals = ct.Ins.Where(p => !p.IsGhost).ToList();
      var parameters = nonGhostFormals.Comma(p => $"{TypeName(p.Type, w, p.tok)} {IdName(p)}");

      // here's the initializer method
      w.Write($"public void {IdName(ct)}({parameters})");
      var wBody = w.NewBlock();
      foreach (var p in nonGhostFormals) {
        wBody.WriteLine("this.{0} = {0};", IdName(p));
      }

      wBody.WriteLine("this._iter = TheIterator();");
      // here are the enumerator methods
      w.WriteLine("public bool MoveNext() { return _iter.MoveNext(); }");
      var wIter = w.NewBlock("private System.Collections.Generic.IEnumerator<object> TheIterator()");
      var beforeYield = wIter.Fork();
      wIter.WriteLine("yield break;");
      return beforeYield;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      var w = CompileDatatypeBase(dt, wr);
      CompileDatatypeConstructors(dt, wr);
      return w;
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      Contract.Requires(dt != null);
      Contract.Requires(wr != null);

      // public abstract class Dt<T> {  // for record types: drop "abstract"
      //   public Dt() { }
      //   #if TypeArgs.Count == 0
      //     private static Dt<T> theDefault = ...;
      //     public static Dt<T> Default(values...) {
      //       return theDefault;
      //     }
      //   #else
      //     public static Dt<T> Default(values...) {
      //       return ...;
      //     }
      //   #endif
      //   public static TypeDescriptor<Dt<T>> _TypeDescriptor(typeDescriptors...) {
      //     return new TypeDescriptor<Dt<T>>(Default(typeDescriptors...));
      //   }
      //   public abstract Dt<T> _Get();  // for co-datatypes
      //
      //   public static create_Ctor0(field0, field1, ...) {  // for record types: create
      //     return new Dt_Ctor0(field0, field1, ...);        // for record types: new Dt
      //   }
      //   ...
      //
      //   public bool is_Ctor0 { get { return this is Dt_Ctor0; } }  // for record types: return true
      //   ...
      //
      //   public T0 dtor_Dtor0 { get {
      //       var d = this;         // for inductive datatypes
      //       var d = this._Get();  // for co-inductive datatypes
      //       if (d is DT_Ctor0) { return ((DT_Ctor0)d).Dtor0; }
      //       if (d is DT_Ctor1) { return ((DT_Ctor1)d).Dtor0; }
      //       ...
      //       if (d is DT_Ctor(n-2)) { return ((DT_Ctor(n-2))d).Dtor0; }
      //       return ((DT_Ctor(n-1))d).Dtor0;  // for record types: drop cast
      //    }}
      //   ...
      // }
      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);
      var DtT_TypeArgs = TypeParameters(nonGhostTypeArgs);
      var DtT_protected = IdName(dt) + DtT_TypeArgs;

      // from here on, write everything into the new block created here:
      var btw = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      wr = btw;

      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine($"public {IdName(dt)}() {{ }}");
      }

      var wDefault = new ConcreteSyntaxTree();
      if (nonGhostTypeArgs.Count == 0) {
        wr.FormatLine($"private static readonly {DtT_protected} theDefault = {wDefault};");
        var w = wr.NewBlock($"public static {DtT_protected} Default()");
        w.WriteLine("return theDefault;");
      } else {
        var parameters = UsedTypeParameters(dt).Comma(tp => $"{tp.CompileName} {FormatDefaultTypeParameterValue(tp)}");
        wr.Write($"public static {DtT_protected} Default({parameters})");
        var w = wr.NewBlock();
        w.FormatLine($"return {wDefault};");
      }

      var groundingCtor = dt.GetGroundingCtor();
      if (dt is CoDatatypeDecl) {
        var wCo = wDefault;
        wDefault = new ConcreteSyntaxTree();
        wCo.Format($"new {dt.CompileName}__Lazy{DtT_TypeArgs}(() => {{ return {wDefault}; }})");
      }

      wDefault.Write(DtCreateName(groundingCtor));
      var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost);
      wDefault.Write($"({nonGhostFormals.Comma(f => DefaultValue(f.Type, wDefault, f.tok))})");

      EmitTypeDescriptorMethod(dt, wr);

      if (dt is CoDatatypeDecl) {
        wr.WriteLine($"public abstract {DtT_protected} _Get();");
      }

      // create methods
      foreach (var ctor in dt.Ctors) {
        wr.Write($"public static {DtT_protected} {DtCreateName(ctor)}(");
        WriteFormals("", ctor.Formals, wr);
        var w = wr.NewBlock(")");
        var arguments = ctor.Formals.Where(f => !f.IsGhost).Comma(FormalName);
        w.WriteLine($"return new {DtCtorDeclarationName(ctor)}{DtT_TypeArgs}({arguments});");
      }

      // query properties
      if (dt is TupleTypeDecl) {
        // omit the is_ property for tuples, since it cannot be used syntactically in the language
      } else {
        foreach (var ctor in dt.Ctors) {
          var returnValue = dt.IsRecordType
            // public bool is_Ctor0 { get { return true; } }
            ? "true"
            // public bool is_Ctor0 { get { return this is Dt_Ctor0; } }
            : $"this is {dt.CompileName}_{ctor.CompileName}{DtT_TypeArgs}";
          wr.WriteLine($"public bool is_{ctor.CompileName} {{ get {{ return {returnValue}; }} }}");
        }
      }

      if (dt.HasFinitePossibleValues) {
        Contract.Assert(nonGhostTypeArgs.Count == 0);
        var w = wr.NewNamedBlock(
          $"public static System.Collections.Generic.IEnumerable<{DtT_protected}> AllSingletonConstructors");
        var wGet = w.NewBlock("get");
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          wGet.WriteLine($"yield return {DtT_protected}.{DtCreateName(ctor)}();");
        }
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              //   public T0 dtor_Dtor0 { get {
              //       var d = this;         // for inductive datatypes
              //       var d = this._Get();  // for co-inductive datatypes
              //       if (d is DT_Ctor0) { return ((DT_Ctor0)d).Dtor0; }
              //       if (d is DT_Ctor1) { return ((DT_Ctor1)d).Dtor0; }
              //       ...
              //       if (d is DT_Ctor(n-2)) { return ((DT_Ctor(n-2))d).Dtor0; }
              //       return ((DT_Ctor(n-1))d).Dtor0;
              //    }}
              var wDtor = wr.NewNamedBlock($"public {TypeName(arg.Type, wr, arg.tok)} dtor_{arg.CompileName}");
              var wGet = wDtor.NewBlock("get");
              if (dt.IsRecordType) {
                if (dt is CoDatatypeDecl) {
                  wGet.WriteLine($"return this._Get().{IdName(arg)};");
                } else {
                  wGet.WriteLine($"return this.{IdName(arg)};");
                }
              } else {
                if (dt is CoDatatypeDecl) {
                  wGet.WriteLine("var d = this._Get();");
                } else {
                  wGet.WriteLine("var d = this;");
                }

                var n = dtor.EnclosingCtors.Count;
                for (int i = 0; i < n - 1; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  var type = $"{dt.CompileName}_{ctor_i.CompileName}{DtT_TypeArgs}";
                  // TODO use pattern matching to replace cast.
                  wGet.WriteLine($"if (d is {type}) {{ return (({type})d).{IdName(arg)}; }}");
                }

                Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n - 1].CompileName);
                wGet.WriteLine(
                  $"return (({dt.CompileName}_{dtor.EnclosingCtors[n - 1].CompileName}{DtT_TypeArgs})d).{IdName(arg)}; ");
              }
            }
          }
        }
      }

      return new ClassWriter(this, btw, null);
    }

    string NeedsNew(TopLevelDeclWithMembers ty, string memberName) {
      Contract.Requires(ty != null);
      Contract.Requires(memberName != null);
      if (ty.Members.Exists(member => member.Name == memberName)) {
        return "new ";
      } else {
        return "";
      }
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, ConcreteSyntaxTree wrx) {
      Contract.Requires(dt != null);
      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);
      string typeParams = TypeParameters(nonGhostTypeArgs);
      if (dt is CoDatatypeDecl) {
        // public class Dt__Lazy<T> : Dt<T> {
        //   public delegate Dt<T> Computer();
        //   Computer c;
        //   Dt<T> d;
        //   public Dt__Lazy(Computer c) { this.c = c; }
        //   public override Dt<T> _Get() { if (c != null) { d = c(); c = null; } return d; }
        //   public override string ToString() { return _Get().ToString(); }
        // }
        var w = wrx.NewNamedBlock($"public class {dt.CompileName}__Lazy{typeParams} : {IdName(dt)}{typeParams}");
        w.WriteLine($"public {NeedsNew(dt, "Computer")}delegate {dt.CompileName}{typeParams} Computer();");
        w.WriteLine($"{NeedsNew(dt, "c")}Computer c;");
        w.WriteLine($"{NeedsNew(dt, "d")}{dt.CompileName}{typeParams} d;");
        w.WriteLine($"public {dt.CompileName}__Lazy(Computer c) {{ this.c = c; }}");
        w.WriteLine($"public override {dt.CompileName}{typeParams} _Get() {{ if (c != null) {{ d = c(); c = null; }} return d; }}");
        w.WriteLine("public override string ToString() { return _Get().ToString(); }");
      }

      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }

      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var wr = wrx.NewNamedBlock(
          $"public class {DtCtorDeclarationName(ctor)}{TypeParameters(nonGhostTypeArgs)} : {IdName(dt)}{typeParams}");
        DatatypeFieldsAndConstructor(ctor, constructorIndex, wr);
        constructorIndex++;
      }
    }

    void DatatypeFieldsAndConstructor(DatatypeCtor ctor, int constructorIndex, ConcreteSyntaxTree wr) {
      Contract.Requires(ctor != null);
      Contract.Requires(0 <= constructorIndex && constructorIndex < ctor.EnclosingDatatype.Ctors.Count);
      Contract.Requires(wr != null);

      var dt = ctor.EnclosingDatatype;
      // class Dt_Ctor<T,U> : Dt<T> {  // This line is to be added by the caller of DatatypeFieldsAndConstructor
      //   Fields;
      //   public Dt_Ctor(arguments) {  // for record types: Dt
      //     Fields = arguments;
      //   }
      //   public override Dt<T> _Get() { return this; }  // for co-datatypes only
      //   public override bool Equals(object other) {
      //     var oth = other as Dt_Ctor;  // for record types: Dt
      //     return oth != null && equals(_field0, oth._field0) && ... ;
      //   }
      //   public override int GetHashCode() {
      //     return base.GetHashCode();  // surely this can be improved
      //   }
      //   public override string ToString() {  // only for inductive datatypes
      //     // ...
      //   }
      // }

      var i = 0;
      foreach (Formal arg in ctor.Formals) {
        if (!arg.IsGhost) {
          wr.WriteLine($"public readonly {TypeName(arg.Type, wr, arg.tok)} {FormalName(arg, i)};");
          i++;
        }
      }

      wr.Write($"public {DtCtorDeclarationName(ctor)}(");
      WriteFormals("", ctor.Formals, wr);
      {
        var w = wr.NewBlock(")");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine($"this.{FormalName(arg, i)} = {FormalName(arg, i)};");
            i++;
          }
        }
      }

      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);

      if (dt is CoDatatypeDecl) {
        string typeParams = TypeParameters(nonGhostTypeArgs);
        wr.WriteLine($"public override {dt.CompileName}{typeParams} _Get() {{ return this; }}");
      }

      // Equals method
      {
        var w = wr.NewBlock("public override bool Equals(object other)");
        w.WriteLine($"var oth = other as {DtCtorName(ctor)}{TypeParameters(nonGhostTypeArgs)};");
        w.Write("return oth != null");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            if (IsDirectlyComparable(arg.Type)) {
              w.Write($" && this.{nm} == oth.{nm}");
            } else {
              w.Write($" && object.Equals(this.{nm}, oth.{nm})");
            }

            i++;
          }
        }

        w.WriteLine(";");
      }

      // GetHashCode method (Uses the djb2 algorithm)
      {
        var w = wr.NewBlock("public override int GetHashCode()");
        w.WriteLine("ulong hash = 5381;");
        w.WriteLine($"hash = ((hash << 5) + hash) + {constructorIndex};");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            w.WriteLine($"hash = ((hash << 5) + hash) + ((ulong){DafnyHelpersClass}.GetHashCode(this.{nm}));");
            i++;
          }
        }

        w.WriteLine("return (int) hash;");
      }

      {
        var w = wr.NewBlock("public override string ToString()");
        string nm;
        if (dt is TupleTypeDecl) {
          nm = "";
        } else {
          nm = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") + dt.Name + "." + ctor.Name;
        }

        switch (dt) {
          case TupleTypeDecl tupleDt when ctor.Formals.Count == 0:
            // here we want parentheses and no name
            w.WriteLine("return \"()\";");
            break;
          case CoDatatypeDecl _:
            w.WriteLine($"return \"{nm}\";");
            break;
          default:
            var tempVar = GenVarName("s", ctor.Formals);
            w.WriteLine($"string {tempVar} = \"{nm}\";");
            if (ctor.Formals.Count != 0) {
              w.WriteLine($"{tempVar} += \"(\";");
              i = 0;
              foreach (var arg in ctor.Formals) {
                if (!arg.IsGhost) {
                  if (i != 0) {
                    w.WriteLine($"{tempVar} += \", \";");
                  }

                  w.WriteLine($"{tempVar} += {DafnyHelpersClass}.ToString(this.{FormalName(arg, i)});");
                  i++;
                }
              }

              w.WriteLine($"{tempVar} += \")\";");
            }

            w.WriteLine($"return {tempVar};");
            break;
        }
      }
    }

    /// <summary>
    /// Returns a protected name.
    /// </summary>
    string DtCtorDeclarationName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      return dt.IsRecordType ? IdName(dt) : dt.CompileName + "_" + ctor.CompileName;
    }

    /// <summary>
    /// Returns a protected name with type parameters.
    /// </summary>
    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs, ConcreteSyntaxTree wr) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeArgs != null && typeArgs.Count != 0) {
        s += $"<{TypeNames(typeArgs, wr, ctor.tok)}>";
      }

      return s;
    }

    /// <summary>
    /// Returns a protected name. (No type parameters.)
    /// </summary>
    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      var dtName = dt.EnclosingModuleDefinition.IsDefaultModule ? IdProtect(dt.CompileName) : dt.FullCompileName;
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }

    string DtCreateName(DatatypeCtor ctor) {
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      } else {
        return "create_" + ctor.CompileName;
      }
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter) CreateClass(IdProtect(nt.EnclosingModuleDefinition.CompileName), IdName(nt), nt, wr);
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var wEnum = w.NewBlock($"public static System.Collections.Generic.IEnumerable<{GetNativeTypeName(nt.NativeType)}> IntegerRange(BigInteger lo, BigInteger hi)");
        wEnum.WriteLine($"for (var j = lo; j < hi; j++) {{ yield return ({GetNativeTypeName(nt.NativeType)})j; }}");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var wrWitness = new ConcreteSyntaxTree();
        TrExpr(nt.Witness, wrWitness, false);
        var witness = wrWitness.ToString();
        string typeName;
        if (nt.NativeType == null) {
          typeName = TypeName(nt.BaseType, cw.StaticMemberWriter, nt.tok);
        } else {
          typeName = GetNativeTypeName(nt.NativeType);
          witness = $"({typeName})({witness})";
        }
        DeclareField("Witness", true, true, true, typeName, witness, cw);
      }
      EmitTypeDescriptorMethod(nt, w);
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter) CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var sw = new ConcreteSyntaxTree(cw.InstanceMemberWriter.RelativeIndentLevel);
        TrExpr(sst.Witness, sw, false);
        var witness = sw.ToString();
        var typeName = TypeName(sst.Rhs, cw.StaticMemberWriter, sst.tok);
        if (sst.TypeArgs.Count == 0) {
          DeclareField("Witness", false, true, true, typeName, witness, cw);
          witness = "Witness";
        }
        var w = cw.StaticMemberWriter.NewBlock($"public static {typeName} Default()");
        w.WriteLine($"return {witness};");
      }
      EmitTypeDescriptorMethod(sst, cw.StaticMemberWriter);
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "byte";
          literalSuffix = "";
          needsCastAfterArithmetic = true;
          break;
        case NativeType.Selection.SByte:
          name = "sbyte";
          literalSuffix = "";
          needsCastAfterArithmetic = true;
          break;
        case NativeType.Selection.UShort:
          name = "ushort";
          literalSuffix = "";
          needsCastAfterArithmetic = true;
          break;
        case NativeType.Selection.Short:
          name = "short";
          literalSuffix = "";
          needsCastAfterArithmetic = true;
          break;
        case NativeType.Selection.UInt:
          name = "uint";
          literalSuffix = "U";
          needsCastAfterArithmetic = false;
          break;
        case NativeType.Selection.Int:
          name = "int";
          literalSuffix = "";
          needsCastAfterArithmetic = false;
          break;
        case NativeType.Selection.Number:
          name = "number";
          literalSuffix = "";
          needsCastAfterArithmetic = false;
          break;
        case NativeType.Selection.ULong:
          name = "ulong";
          literalSuffix = "UL";
          needsCastAfterArithmetic = false;
          break;
        case NativeType.Selection.Long:
          name = "long";
          literalSuffix = "L";
          needsCastAfterArithmetic = false;
          break;
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter
    {
      public readonly CsharpCompiler Compiler;
      public readonly ConcreteSyntaxTree InstanceMemberWriter;
      public readonly ConcreteSyntaxTree StaticMemberWriter;
      public readonly ConcreteSyntaxTree CtorBodyWriter;

      public ClassWriter(CsharpCompiler compiler, ConcreteSyntaxTree instanceMemberWriter, ConcreteSyntaxTree/*?*/ ctorBodyWriter, ConcreteSyntaxTree/*?*/ staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.CtorBodyWriter = ctorBodyWriter;
        this.StaticMemberWriter = staticMemberWriter ?? instanceMemberWriter;
      }

      public ConcreteSyntaxTree Writer(bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        if (createBody) {
          if (isStatic || member?.EnclosingClass is TraitDecl && NeedsCustomReceiver(member)) {
            return StaticMemberWriter;
          }
        }

        return InstanceMemberWriter;
      }

      public ConcreteSyntaxTree /*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, Writer(m.IsStatic, createBody, m), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree /*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic, createBody, member), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree /*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, Bpl.IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl /*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic, createBody, member));
      }

      public ConcreteSyntaxTree /*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl /*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic, createBody, member));
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, Field field) {
        var typeName = Compiler.TypeName(type, this.StaticMemberWriter, tok);
        Compiler.DeclareField(name, true, isStatic, isConst, typeName, rhs, this);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new NotSupportedException(); // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
      }

      public ConcreteSyntaxTree /*?*/ ErrorWriter() => InstanceMemberWriter;

      public void Finish() { }
    }

    protected ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var hasDllImportAttribute = ProcessDllImport(m, wr);
      var customReceiver = createBody && !forBodyInheritance && NeedsCustomReceiver(m);
      var keywords = Keywords(createBody, m.IsStatic || customReceiver, hasDllImportAttribute);
      var returnType = GetTargetReturnTypeReplacement(m, wr);
      AddTestCheckerIfNeeded(m.Name, m, wr);
      var typeParameters = TypeParameters(TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, m, lookasideBody)));
      var parameters = GetMethodParameters(m, typeArgs, lookasideBody, customReceiver, returnType);
      wr.Format($"{keywords}{returnType} {IdName(m)}{typeParameters}({parameters})");

      if (!createBody || hasDllImportAttribute) {
        wr.WriteLine(";");
        return null;
      }

      var block = wr.NewBlock(open: BraceStyle.Newline);
      if (returnType != "void" && !forBodyInheritance) {
        var beforeReturnBlock = block.Fork();
        EmitReturn(m.Outs, block);
        return beforeReturnBlock;
      }

      return block;
    }

    static string Keywords(bool isPublic = false, bool isStatic = false, bool isExtern = false) {
      return (isPublic ? "public " : "") + (isStatic ? "static " : "") + (isExtern ? "extern " : "");
    }

    private ConcreteSyntaxTree GetMethodParameters(Method m, List<TypeArgumentInstantiation> typeArgs, bool lookasideBody, bool customReceiver, string returnType) {
      var parameters = GetFunctionParameters(m.Ins, m, typeArgs, lookasideBody, customReceiver);
      if (returnType == "void") {
        WriteFormals(parameters.Nodes.Any() ? ", " : "", m.Outs, parameters);
      }
      return parameters;
    }

  private ConcreteSyntaxTree GetFunctionParameters(List<Formal> formals, MemberDecl m, List<TypeArgumentInstantiation> typeArgs, bool lookasideBody, bool customReceiver) {
      var parameters = new ConcreteSyntaxTree();
      var sep = "";
      WriteRuntimeTypeDescriptorsFormals(m, ForTypeDescriptors(typeArgs, m, lookasideBody), parameters, ref sep,
        tp => $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
      if (customReceiver) {
        var nt = m.EnclosingClass;
        var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, nt);
        DeclareFormal(sep, "_this", receiverType, m.tok, true, parameters);
        sep = ", ";
      }

      WriteFormals(sep, formals, parameters);
      return parameters;
    }

    private string GetTargetReturnTypeReplacement(Method m, ConcreteSyntaxTree wr) {
      string/*?*/ targetReturnTypeReplacement = null;
      foreach (var p in m.Outs) {
        if (!p.IsGhost) {
          if (targetReturnTypeReplacement == null) {
            targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
          } else {
            // there's more than one out-parameter, so bail
            targetReturnTypeReplacement = null;
            break;
          }
        }
      }

      targetReturnTypeReplacement ??= "void";
      return targetReturnTypeReplacement;
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var hasDllImportAttribute = ProcessDllImport(member, wr);

      var customReceiver = createBody && !forBodyInheritance && NeedsCustomReceiver(member);

      AddTestCheckerIfNeeded(name, member, wr);
      wr.Write(Keywords(createBody, isStatic || customReceiver, hasDllImportAttribute));
      
      var typeParameters = TypeParameters(TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, member, lookasideBody)));
      var parameters = GetFunctionParameters(formals, member, typeArgs, lookasideBody, customReceiver);
      
      wr.Write($"{TypeName(resultType, wr, tok)} {name}{typeParameters}({parameters})");
      if (!createBody || hasDllImportAttribute) {
        wr.WriteLine(";");
        return null;
      }

      return wr.NewBlock(open: formals.Count > 1 ? BraceStyle.Newline : BraceStyle.Space);
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree/*?*/ result = null;
      var body = createBody ? Block(out result, close: BraceStyle.Nothing) : new ConcreteSyntaxTree().Write(";");
      wr.FormatLine($"{Keywords(createBody, isStatic)}{TypeName(resultType, wr, tok)} {name} {{ get{body} }}");
      return result;
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree wr) {
      wr.Write($"{Keywords(createBody, isStatic)}{TypeName(resultType, wr, tok)} {name}");
      if (createBody) {
        var w = wr.NewBlock();
        var wGet = w.NewBlock("get");
        var wSet = w.NewBlock("set");
        setterWriter = wSet;
        return wGet;
      } else {
        wr.WriteLine(" { get; set; }");
        setterWriter = null;
        return null;
      }
    }

    /// <summary>
    /// Process the declaration's "dllimport" attribute, if any, by emitting the corresponding .NET custom attribute.
    /// Returns "true" if the declaration has an active "dllimport" attribute; "false", otherwise.
    /// </summary>
    public bool ProcessDllImport(MemberDecl decl, ConcreteSyntaxTree wr) {
      Contract.Requires(decl != null);
      Contract.Requires(wr != null);

      var dllimportsArgs = Attributes.FindExpressions(decl.Attributes, "dllimport");
      if (!DafnyOptions.O.DisallowExterns && dllimportsArgs != null) {
        StringLiteralExpr libName = null;
        StringLiteralExpr entryPoint = null;
        if (dllimportsArgs.Count == 2) {
          libName = dllimportsArgs[0] as StringLiteralExpr;
          entryPoint = dllimportsArgs[1] as StringLiteralExpr;
        } else if (dllimportsArgs.Count == 1) {
          libName = dllimportsArgs[0] as StringLiteralExpr;
          // use the given name, not the .CompileName (if user needs something else, the user can supply it as a second argument to :dllimport)
          entryPoint = new StringLiteralExpr(decl.tok, decl.Name, false);
        }
        if (libName == null || entryPoint == null) {
          Error(decl.tok, "Expected arguments are {{:dllimport dllName}} or {{:dllimport dllName, entryPoint}} where dllName and entryPoint are strings: {0}", wr, decl.FullName);
        } else if ((decl is Method m && m.Body != null) || (decl is Function f && f.Body != null)) {
          Error(decl.tok, "A {0} declared with :dllimport is not allowed a body: {1}", wr, decl.WhatKind, decl.FullName);
        } else if (!decl.IsStatic) {
          Error(decl.tok, "A {0} declared with :dllimport must be static: {1}", wr, decl.WhatKind, decl.FullName);
        } else {
          wr.Write("[System.Runtime.InteropServices.DllImport(");
          TrStringLiteral(libName, wr);
          wr.Write(", EntryPoint=");
          TrStringLiteral(entryPoint, wr);
          wr.WriteLine(")]");
        }
        return true;
      }
      return false;
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      Contract.Assume((member is Method m0 && m0.IsTailRecursive) || (member is Function f0 && f0.IsTailRecursive)); // precondition
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        wr.WriteLine("var _this = this;");
      }
      wr.Fork(-1).WriteLine("TAIL_CALL_START: ;");
      return wr;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START;");
    }

    protected override string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "object";
      }

      if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return "char";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigInteger";
      } else if (xType is RealType) {
        return "Dafny.BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigInteger";
      } else if (xType.AsNewtype != null && member == null) {  // when member is given, use UserDefinedType case below
        var nativeType = xType.AsNewtype.NativeType;
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
        TypeName_SplitArrayName(elType, wr, tok, out string typeNameSansBrackets, out string brackets);
        return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets;
      } else if (xType is UserDefinedType udt) {
        if (udt.ResolvedClass is TypeParameter tp) {
          if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(tp, out var instantiatedTypeParameter)) {
            return TypeName(instantiatedTypeParameter, wr, tok, member);
          }
        }
        var s = FullTypeName(udt, member);
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "ulong";
        }
        return TypeName_UDT(s, udt, wr, udt.tok);
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        return DafnyISet + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        return DafnyISeq + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        return DafnyIMultiset + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        return DafnyIMap + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public string TypeHelperName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, Type/*?*/ otherType = null) {
      var xType = type.NormalizeExpand();
      if (xType is SeqType seqType) {
        return "Dafny.Sequence" + "<" + CommonTypeName(seqType.Arg, otherType?.AsSeqType?.Arg, wr, tok) + ">";
      } else if (xType is SetType setType) {
        return $"{DafnySetClass}<{CommonTypeName(setType.Arg, otherType?.AsSetType?.Arg, wr, tok)}>";
      } else if (xType is MultiSetType msType) {
        return $"{DafnyMultiSetClass}<{CommonTypeName(msType.Arg, otherType?.AsMultiSetType?.Arg, wr, tok)}>";
      } else if (xType is MapType mapType) {
        var domainType = CommonTypeName(mapType.Domain, otherType?.AsMapType?.Domain, wr, tok);
        var rangeType = CommonTypeName(mapType.Range, otherType?.AsMapType?.Range, wr, tok);
        return $"{DafnyMapClass}<{domainType}, {rangeType}>";
      } else {
        return TypeName(type, wr, tok);
      }
    }

    public string CommonTypeName(Type a, Type /*?*/ b, ConcreteSyntaxTree wr, Bpl.IToken tok) {
      if (b == null) {
        return TypeName(a, wr, tok);
      }
      a = a.NormalizeExpand();
      b = b.NormalizeExpand();
      if (a.Equals(b)) {
        return TypeName(a, wr, tok);
      }
      // It would be nice to use Meet(a, b) here. Unfortunately, Resolver.Meet also needs a Builtins argument, which we
      // don't have here.
      Contract.Assert(a.IsRefType);
      Contract.Assert(b.IsRefType);
      return "object";
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();

      if (usePlaceboValue) {
        return $"default({TypeName(type, wr, tok)})";
      }

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return CharType.DefaultValueAsString;
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigInteger.Zero";
      } else if (xType is RealType) {
        return "Dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "BigInteger.Zero";
      } else if (xType is CollectionType) {
        return TypeHelperName(xType, wr, tok) + ".Empty";
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter tp) {
        if (constructTypeParameterDefaultsFromTypeDescriptors) {
          return $"{FormatTypeDescriptorVariable(tp.CompileName)}.Default()";
        } else {
          return FormatDefaultTypeParameterValue(tp);
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
          return TypeName_UDT(FullTypeName(udt), udt, wr, udt.tok) + ".Default()";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return $"(({TypeName(xType, wr, udt.tok)})null)";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            var arguments = Util.Comma(udt.TypeArgs.Count - 1, i => $"{TypeName(udt.TypeArgs[i], wr, udt.tok)} x{i}");
            return $"(({arguments}) => {rangeDefaultValue})";
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out string typeNameSansBrackets, out string brackets);
            return $"new {typeNameSansBrackets}[{Util.Comma(arrayClass.Dims, _ => "0")}]{brackets}";
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return $"default({TypeName(xType, wr, udt.tok)})";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return $"({TypeName(xType, wr, udt.tok)})null";
        }
      } else if (cl is DatatypeDecl dt) {
        var s = FullTypeName(udt);
        var nonGhostTypeArgs = SelectNonGhost(dt, udt.TypeArgs);
        if (nonGhostTypeArgs.Count != 0) {
          s += "<" + TypeNames(nonGhostTypeArgs, wr, udt.tok) + ">";
        }
        var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs);
        return string.Format($"{s}.Default({relevantTypeArgs.Comma(ta => DefaultValue(ta.Actual, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))})");
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs, ConcreteSyntaxTree wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance.Count == typeArgs.Count);
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0) {
        for (var i = 0; i < typeArgs.Count; i++) {
          var v = variance[i];
          var ta = typeArgs[i];
          if (ComplicatedTypeParameterForCompilation(v, ta)) {
            Error(tok, "compilation does not support trait types as a type parameter (got '{0}'{1}); consider introducing a ghost", wr,
              ta, typeArgs.Count == 1 ? "" : $" for type parameter {i}");
          }
        }
        s += "<" + TypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, MemberDecl/*?*/ member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      if (type is UserDefinedType udt && udt.ResolvedClass is TraitDecl) {
        return TypeName_UDT(udt.FullCompanionCompileName, udt, wr, tok);
      } else {
        return TypeName(type, wr, tok, member);
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

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok) {
      type = type.NormalizeExpandKeepConstraints();
      if (type is BoolType) {
        return "Dafny.Helpers.BOOL";
      } else if (type is CharType) {
        return "Dafny.Helpers.CHAR";
      } else if (type is IntType || type is BigOrdinalType) {
        return "Dafny.Helpers.INT";
      } else if (type is RealType) {
        return "Dafny.Helpers.REAL";
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        if (t.NativeType != null) {
          return GetNativeTypeDescriptor(AsNativeType(type));
        } else {
          return "Dafny.Helpers.INT";
        }
      } else if (type is SetType setType) {
        return $"{DafnySetClass}<{TypeName(setType.Arg, wr, tok)}>.{TypeDescriptorMethodName}()";
      } else if (type is SeqType seqType) {
        return $"{DafnySeqClass}<{TypeName(seqType.Arg, wr, tok)}>.{TypeDescriptorMethodName}()";
      } else if (type is MultiSetType multisetType) {
        return $"{DafnyMultiSetClass}<{TypeName(multisetType.Arg, wr, tok)}>.{TypeDescriptorMethodName}()";
      } else if (type is MapType mapType) {
        return $"{DafnyMapClass}<{TypeName(mapType.Domain, wr, tok)}, {TypeName(mapType.Range, wr, tok)}>.{TypeDescriptorMethodName}()";
      } else if (type.IsRefType) {
        return $"Dafny.Helpers.NULL<{TypeName(type, wr, tok)}>()";
      } else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        var elType = UserDefinedType.ArrayElementType(type);
        var elTypeName = TypeName(elType, wr, tok);
        return $"Dafny.Helpers.ARRAY{(at.Dims == 1 ? "" : $"{at.Dims}")}<{elTypeName}>()";
      } else if (type.IsTypeParameter) {
        var tp = type.AsTypeParameter;
        Contract.Assert(tp != null);
        if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(tp, out var instantiatedTypeParameter)) {
          return TypeDescriptor(instantiatedTypeParameter, wr, tok);
        }
        return FormatTypeDescriptorVariable(type.AsTypeParameter.CompileName);
      } else if (type.IsBuiltinArrowType) {
        return $"Dafny.Helpers.NULL<{TypeName(type, wr, tok)}>()";
      } else if (type is UserDefinedType udt) {
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "Dafny.Helpers.INT64";
        }

        List<Type> relevantTypeArgs;
        if (type.IsBuiltinArrowType) {
          relevantTypeArgs = type.TypeArgs;
        } else if (cl is DatatypeDecl dt) {
          relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs).ConvertAll(ta => ta.Actual);
        } else {
          relevantTypeArgs = new List<Type>();
          for (int i = 0; i < cl.TypeArgs.Count; i++) {
            if (NeedsTypeDescriptor(cl.TypeArgs[i])) {
              relevantTypeArgs.Add(udt.TypeArgs[i]);
            }
          }
        }

        return AddTypeDescriptorArgs(FullTypeName(udt), udt, relevantTypeArgs, wr, tok);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private string GetNativeTypeDescriptor(NativeType nt) {
      Contract.Assert(nt != null);
      switch (nt.Sel) {
        case NativeType.Selection.SByte:
          return $"Dafny.Helpers.INT8";
        case NativeType.Selection.Byte:
          return $"Dafny.Helpers.UINT8";
        case NativeType.Selection.Short:
          return $"Dafny.Helpers.INT16";
        case NativeType.Selection.UShort:
          return $"Dafny.Helpers.UINT16";
        case NativeType.Selection.Int:
          return $"Dafny.Helpers.INT32";
        case NativeType.Selection.UInt:
          return $"Dafny.Helpers.UINT32";
        case NativeType.Selection.Long:
          return $"Dafny.Helpers.INT64";
        case NativeType.Selection.ULong:
          return $"Dafny.Helpers.UINT64";
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private string AddTypeDescriptorArgs(string fullCompileName, UserDefinedType udt, List<Type> typeDescriptors, ConcreteSyntaxTree wr, Bpl.IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(udt != null);
      Contract.Requires(typeDescriptors != null);
      Contract.Requires(wr != null);
      Contract.Requires(tok != null);

      var s = TypeName_UDT(fullCompileName, udt, wr, tok);
      s += $"._TypeDescriptor({typeDescriptors.Comma(arg => TypeDescriptor(arg, wr, tok))})";
      return s;
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isPublic, bool isStatic, bool isConst, string typeName, string rhs, ClassWriter cw) {
      var publik = isPublic ? "public" : "private";
      var konst = isConst ? " readonly" : "";
      if (isStatic) {
        cw.StaticMemberWriter.Write($"{publik} static{konst} {typeName} {name}");
        if (rhs != null) {
          cw.StaticMemberWriter.Write($" = {rhs}");
        }
        cw.StaticMemberWriter.WriteLine(";");
      } else if (cw.CtorBodyWriter == null) {
        cw.InstanceMemberWriter.Write($"{publik}{konst} {typeName} {name}");
        if (rhs != null) {
          cw.InstanceMemberWriter.Write($" = {rhs}");
        }
        cw.InstanceMemberWriter.WriteLine(";");
      } else {
        cw.InstanceMemberWriter.Write($"{publik} {typeName} {name};");
        if (rhs != null) {
          cw.CtorBodyWriter.WriteLine($"this.{name} = {rhs};");
        }
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      wr.Write($"{prefix}{(isInParam ? "" : "out ")}{TypeName(type, wr, tok)} {name}");
      return true;
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, ConcreteSyntaxTree wr) {
      wr.Write($"{(type != null ? TypeName(type, wr, tok) : "var")} {name}");
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine($" = {rhs};");
      } else {
        wr.WriteLine(";");
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, ConcreteSyntaxTree wr) {
      var w = new ConcreteSyntaxTree();
      wr.FormatLine($"{(type != null ? TypeName(type, wr, tok) : "var")} {name} = {w};");
      return w;
    }

    protected override void DeclareOutCollector(string collectorVarName, ConcreteSyntaxTree wr) {
      wr.Write($"var {collectorVarName} = ");
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      if (useReturnStyleOuts) {
        DeclareLocalVar(name, type, tok, false, rhs, wr);
      } else {
        EmitAssignment(name, type, rhs, null, wr);
      }
    }

    protected override void EmitActualOutArg(string actualOutParamName, ConcreteSyntaxTree wr) {
      wr.Write($"out {actualOutParamName}");
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) {
      return nonGhostOutCount == 1;
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, ConcreteSyntaxTree wr) {
      Contract.Assert(actualOutParamNames.Count == 1);
      EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      if (typeArgs.Count != 0) {
        wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
      }
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, ConcreteSyntaxTree wr, Bpl.IToken tok) {
      return (type != null ? TypeName(type, wr, tok) : "var") + " " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg)
    {
      var typeArgs = arg.Type.AsArrowType == null ? "" : $"<{TypeName(arg.Type, wr, null, null)}>";
      wr.WriteLine($"{DafnyHelpersClass}.Print{typeArgs}({Expr(arg, false)});");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr)
    {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      var returnExpr = outParams.Count == 1 ? IdName(outParams[0]) : "";
      wr.WriteLine($"return {returnExpr};");
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      wr.Fork(-1).WriteLine($"after_{label}: ;");
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, ConcreteSyntaxTree wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("goto after_{0};", label);
      }
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      wr.WriteLine("yield return null;");
    }

    protected override void EmitAbsurd(string/*?*/ message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw new System.Exception(\"{0}\");", message);
    }

    protected override void EmitHalt(Bpl.IToken tok, Expression/*?*/ messageExpr, ConcreteSyntaxTree wr) {
      wr.Write("throw new Dafny.HaltException(");
      if (tok != null) wr.Write(SymbolDisplay.FormatLiteral(ErrorReporter.TokenToString(tok) + ": ", true) + " + ");
      TrExpr(messageExpr, wr, false);
      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(Bpl.IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, ConcreteSyntaxTree wr) {

      wr.Write($"for ({TypeName(loopIndex.Type,wr, tok)} {loopIndex.CompileName} = ");
      var startWr = wr.Fork();
      wr.Write($"; ");

      ConcreteSyntaxTree bodyWr;
      if (goingUp) {
        wr.Write(endVarName != null ? $"{loopIndex.CompileName} < {endVarName}" : "");
        bodyWr = wr.NewBlock($"; {loopIndex.CompileName}++)");
      } else {
        wr.Write(endVarName != null ? $"{endVarName} < {loopIndex.CompileName}" : "");
        bodyWr = wr.NewBlock($"; )");
        bodyWr.WriteLine($"{loopIndex.CompileName}--;");
      }
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for (var {0} = 0; {0} < {1}; {0}++)", indexVar, bound);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock("for (var {0} = new BigInteger({1}); ; {0} *= 2)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName}++;");
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName}--;");
    }

    protected override string GetQuantifierName(string bvType) {
      return string.Format($"{DafnyHelpersClass}.Quantifier<{bvType}>");
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, string boundVarName, Type boundVarType, bool introduceBoundVar,
      Bpl.IToken tok, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      wr.Format($"foreach ({TypeName(collectionElementType, wr, tok)} {tmpVarName} in {collectionWriter})");
      var wwr = wr.NewBlock();

      if (boundVarType.IsRefType) {
        string typeTest;
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          typeTest = "true";
        } else {
          typeTest = $"{tmpVarName} is {TypeName(boundVarType, wwr, tok)}";
        }
        if (boundVarType.IsNonNullRefType) {
          typeTest = $"{tmpVarName} != null && {typeTest}";
        } else {
          typeTest = $"{tmpVarName} == null || {typeTest}";
        }
        wwr = wwr.NewBlock($"if ({typeTest})");
      }
      var typeName = TypeName(boundVarType, wwr, tok);
      wwr.WriteLine("{0}{1} = ({2}){3};", introduceBoundVar ? typeName + " " : "", boundVarName, typeName, tmpVarName);
      return wwr;
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      return wr.Format($"foreach (var {boundVarName} in {collectionWriter})").NewBlock();
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, ConcreteSyntaxTree wr) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      var ctor = initCall == null ? null : (Constructor)initCall.Method;  // correctness of cast follows from precondition of "EmitNew"
      var arguments = new ConcreteSyntaxTree();
      wr.Format($"new {TypeName(type, wr, tok)}({arguments})");
      var sep = "";
      EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, arguments, ref sep);
      if (ctor != null && ctor.IsExtern(out _, out _)) {
        // the arguments of any external constructor are placed here
        for (int i = 0; i < ctor.Ins.Count; i++) {
          Formal p = ctor.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(initCall.Args[i], arguments, false);
            sep = ", ";
          }
        }
      }
    }

    // if checkRange is false, msg is ignored
    // if checkRange is true and msg is null and the value is out of range, a generic message is emitted
    // if checkRange is true and msg is not null and the value is out of range, msg is emitted in the error message
    protected void TrExprAsInt(Expression expr, ConcreteSyntaxTree wr, bool inLetExprBody, bool checkRange = false,
      string msg = null) {
      wr.Write($"{GetHelperModuleName()}.ToIntChecked(");
      TrExpr(expr, wr, inLetExprBody);
      if (checkRange) wr.Write(msg == null ? ", null" : $", \"{msg}\")");
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, ConcreteSyntaxTree wr) {
      var wrs = EmitNewArray(elmtType, tok, dimensions.Count, mustInitialize, wr);
      for (int i = 0; i < wrs.Count; i++) {
        TrExprAsInt(dimensions[i], wrs[i], inLetExprBody: false, true, "C# arrays may not be larger than the max 32-bit integer");
      }
    }

    private List<ConcreteSyntaxTree> EmitNewArray(Type elmtType, Bpl.IToken tok, int dimCount, bool mustInitialize, ConcreteSyntaxTree wr) {
      var wrs = new List<ConcreteSyntaxTree>();
      if (!mustInitialize || HasSimpleZeroInitializer(elmtType)) {
        TypeName_SplitArrayName(elmtType, wr, tok, out string typeNameSansBrackets, out string brackets);
        wr.Write("new {0}", typeNameSansBrackets);
        string prefix = "[";
        for (var d = 0; d < dimCount; d++) {
          wr.Write($"{prefix}{DafnyHelpersClass}.ToIntChecked(");
          var w = wr.Fork();
          wrs.Add(w);
          wr.Write(",\"C# array size must not be larger than max 32-bit int\")");
          prefix = ", ";
        }
        wr.Write("]{0}", brackets);
      } else {
        wr.Write("Dafny.ArrayHelpers.InitNewArray{0}<{1}>", dimCount, TypeName(elmtType, wr, tok));
        var inParens = wr.ForkInParens();
        inParens.Write(DefaultValue(elmtType, inParens, tok, true));
        for (var d = 0; d < dimCount; d++) {
          inParens.Write(", ");
          var w = inParens.Fork();
          wrs.Add(w);
        }
      }
      return wrs;
    }

    /// <summary>
    /// Return "true" if the C# all-zero bit pattern is a meaningful value for a Dafny type "t".
    /// This method is allowed to be conservative; that is, it is allowed to return "false" more often
    /// than strictly needed.
    /// </summary>
    private bool HasSimpleZeroInitializer(Type t) {
      Contract.Requires(t != null);

      t = t.NormalizeExpandKeepConstraints();
      if (t is CharType) {
        // Okay, so '\0' _is_ a value of type "char", but it's so unpleasant to deal with in test files, etc.
        // By returning false here, a different value will be chosen.
        return false;
      } else if (t is BoolType || t is IntType || t is BigOrdinalType || t is RealType || t is BitvectorType) {
        return true;
      } else if (t is CollectionType) {
        return false;
      }

      var udt = (UserDefinedType)t;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        return td.WitnessKind == SubsetTypeDecl.WKind.CompiledZero;
      } else if (cl is ClassDecl) {
        return true; // null is a value of this type
      } else {
        return false;
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        var cl = (e.Type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          wr.Write("0");
        } else {
          wr.Write("({0})null", TypeName(e.Type, wr, e.tok));
        }
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        wr.Write("'{0}'", (string)e.Value);
      } else if (e is StringLiteralExpr str) {
        wr.Format($"{DafnySeqClass}<char>.FromString({StringLiteral(str)})");
      } else if (AsNativeType(e.Type) != null) {
        string nativeName = null, literalSuffix = null;
        bool needsCastAfterArithmetic = false;
        GetNativeInfo(AsNativeType(e.Type).Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
        wr.Write((BigInteger)e.Value + literalSuffix);
      } else if (e.Value is BigInteger bigInteger) {
        EmitIntegerLiteral(bigInteger, wr);
      } else if (e.Value is BigDec n) {
        if (0 <= n.Exponent) {
          wr.Write("new Dafny.BigRational(BigInteger.Parse(\"{0}", n.Mantissa);
          for (int i = 0; i < n.Exponent; i++) {
            wr.Write("0");
          }
          wr.Write("\"), BigInteger.One)");
        } else {
          wr.Write("new Dafny.BigRational(");
          EmitIntegerLiteral(n.Mantissa, wr);
          wr.Write(", BigInteger.Parse(\"1");
          for (int i = n.Exponent; i < 0; i++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }

    void EmitIntegerLiteral(BigInteger i, ConcreteSyntaxTree wr) {
      Contract.Requires(wr != null);
      if (i.IsZero) {
        wr.Write("BigInteger.Zero");
      } else if (i.IsOne) {
        wr.Write("BigInteger.One");
      } else if (int.MinValue <= i && i <= int.MaxValue) {
        wr.Write($"new BigInteger({i})");
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write($"new BigInteger({i}L)");
      } else if (ulong.MinValue <= i && i <= ulong.MaxValue) {
        wr.Write($"new BigInteger({i}UL)");
      } else {
        wr.Write($"BigInteger.Parse(\"{i}\")");
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      wr.Write($"{(isVerbatim ? "@" : "")}\"{str}\"");
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      // --- Before
      if (bvType.NativeType != null) {
        if (surroundByUnchecked) {
          // Unfortunately, the following will apply "unchecked" to all subexpressions as well.  There
          // shouldn't ever be any problem with this, but stylistically it would have been nice to have
          // applied the "unchecked" only to the actual operation that may overflow.
          wr = wr.Write("unchecked").ForkInParens();
        }
        wr.Write($"({nativeName})");
      }
      wr = wr.ForkInParens();
      // --- Middle
      var middle = wr.ForkInParens();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write(" & ((new BigInteger(1) << {0}) - 1)", bvType.Width);
      } else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          wr.Write(" & ({2})0x{0:X}{1}", (1UL << bvType.Width) - 1, literalSuffix, nativeName);
        }
      }

      return middle;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      // ( e0 op1 e1) | (e0 op2 (width - e1))
      if (needsCast) {
        wr = wr.Write("(" + nativeName + ")").ForkInParens();
      }
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, nativeType, true, wr.ForkInParens(), inLetExprBody, tr);

      wr.Write(" | ");

      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, nativeType, false, wr.ForkInParens(), inLetExprBody, tr);
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType/*?*/ nativeType, bool firstOp, ConcreteSyntaxTree wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody);
      wr.Write(" {0} ", op);
      if (!firstOp) {
        wr = wr.ForkInParens().Write("{0} - ", bv.Width);
      }

      wr.Write("(int)");
      tr(e1, wr.ForkInParens(), inLetExprBody);
    }

    protected override bool CompareZeroUsingSign(Type type) {
      return AsNativeType(type) == null;
    }

    protected override ConcreteSyntaxTree EmitSign(Type type, ConcreteSyntaxTree wr) {
      // Should only be called when CompareZeroUsingSign is true
      Contract.Assert(AsNativeType(type) == null);

      ConcreteSyntaxTree w = wr.Fork();
      wr.Write(".Sign");

      return w;
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.Write($"new System.Collections.Generic.List<System.Tuple<{tupleTypeArgs}>>()");
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      var wrTuple = new ConcreteSyntaxTree();
      wr.FormatLine($"{ingredients}.Add(new System.Tuple<{tupleTypeArgs}>({wrTuple}));");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write($"{prefix}.Item{i+1}");
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public static string PublicIdProtect(string name) {
      if (name == "" || name.First() == '_') {
        return name;  // no need to further protect this name -- we know it's not a C# keyword
      }
      switch (name) {
        // keywords
        case "base":
        case "byte":
        case "catch":
        case "checked":
        case "continue":
        case "decimal":
        case "default":
        case "delegate":
        case "do":
        case "double":
        case "enum":
        case "event":
        case "explicit":
        case "extern":
        case "finally":
        case "fixed":
        case "float":
        case "for":
        case "foreach":
        case "goto":
        case "implicit":
        case "interface":
        case "internal":
        case "is":
        case "lock":
        case "long":
        case "namespace":
        case "operator":
        case "out":
        case "override":
        case "params":
        case "private":
        case "protected":
        case "public":
        case "readonly":
        case "ref":
        case "sbyte":
        case "sealed":
        case "short":
        case "sizeof":
        case "stackalloc":
        case "struct":
        case "switch":
        case "throw":
        case "try":
        case "typeof":
        case "uint":
        case "ulong":
        case "unchecked":
        case "unsafe":
        case "ushort":
        case "using":
        case "virtual":
        case "void":
        case "volatile":
        // contextual keywords
        case "add":
        case "alias":
        case "ascending":
        case "async":
        case "await":
        case "descending":
        case "dynamic":
        case "equals":
        case "from":
        case "get":
        case "global":
        case "group":
        case "into":
        case "join":
        case "let":
        case "nameof":
        case "on":
        case "orderby":
        case "partial":
        case "remove":
        case "select":
        case "set":
        case "value":
        case "when":
        case "where":
          return "@" + name;
        // methods with expected names
        case "ToString":
        case "GetHashCode":
        case "Main":
          return "_" + name;
        default:
          return name;
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null) {
      Contract.Assume(udt != null);  // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      if (member != null && member.IsExtern(out var qualification, out _) && qualification != null) {
        return qualification;
      }
      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.CompileName);
      }

      if (cl.EnclosingModuleDefinition.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      }

      if (cl.IsExtern(out _, out _)) {
        return cl.EnclosingModuleDefinition.CompileName + "." + cl.CompileName;
      }
      return IdProtect(cl.EnclosingModuleDefinition.CompileName) + "." + IdProtect(cl.CompileName);
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      var custom =
        enclosingMethod != null && enclosingMethod.IsTailRecursive ||
        enclosingFunction != null && enclosingFunction.IsTailRecursive ||
        thisContext is NewtypeDecl ||
        thisContext is TraitDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.EnclosingModuleDefinition.IsDefaultModule ? dt.CompileName : dt.FullCompileName;

      var nonGhostInferredTypeArgs = SelectNonGhost(dt, dtv.InferredTypeArgs);
      var typeParams = nonGhostInferredTypeArgs.Count == 0 ? "" : $"<{TypeNames(nonGhostInferredTypeArgs, wr, dtv.tok)}>";
      if (!dtv.IsCoCall) {
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   Dt.create_Cons<T>( args )
        wr.Write($"@{dtName}{typeParams}.{DtCreateName(dtv.Ctor)}({arguments})");
      } else {
        // In the case of a co-recursive call, generate:
        //     new Dt__Lazy<T>( LAMBDA )
        // where LAMBDA is:
        //     () => { return Dt_Cons<T>( ...args... ); }
        wr.Write($"new {dtv.DatatypeName}__Lazy{typeParams}(");
        wr.Write("() => { return ");
        wr.Write("new {0}({1})", DtCtorName(dtv.Ctor, dtv.InferredTypeArgs, wr), arguments);
        wr.Write("; })");
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
          compiledName = idParam == null ? "Length" : $"GetLength({(int) idParam})";
          if (id == SpecialField.ID.ArrayLength) {
            preString = "new BigInteger(";
            postString = ")";
          }
          break;
        case SpecialField.ID.Floor:
          compiledName = "ToBigInteger()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "Dafny.BigOrdinal.IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "Dafny.BigOrdinal.IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "Dafny.BigOrdinal.Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "Dafny.BigOrdinal.IsNat(";
          postString = ")";
          break;
        case SpecialField.ID.Keys:
          compiledName = "Keys";
          break;
        case SpecialField.ID.Values:
          compiledName = "Values";
          break;
        case SpecialField.ID.Items:
          var mapType = receiverType.AsMapType;
          Contract.Assert(mapType != null);
          var errorWr = new ConcreteSyntaxTree();
          var domainType = TypeName(mapType.Domain, errorWr, Bpl.Token.NoToken);
          var rangeType = TypeName(mapType.Range, errorWr, Bpl.Token.NoToken);
          preString = $"{DafnyMapClass}<{domainType}, {rangeType}>.Items(";
          postString = ")";
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
      if (member is SpecialField sf && !(member is ConstantField)) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out string compiledName, out string _, out string _);
        if (compiledName.Length != 0) {
          return SuffixLvalue(obj, ".{0}", compiledName);
        } else {
          // this member selection is handled by some kind of enclosing function call, so nothing to do here
          return SimpleLvalue(obj);
        }
      } else if (member is Function fn) {
        var wr = new ConcreteSyntaxTree();
        EmitNameAndActualTypeArgs(IdName(member), TypeArgumentInstantiation.ToActuals(ForTypeParameters(typeArgs, member, false)), member.tok, wr);
        if (typeArgs.Count == 0 && additionalCustomParameter == null) {
          var nameAndTypeArgs = wr.ToString();
          return SuffixLvalue(obj, $".{nameAndTypeArgs}");
        } else {
          // We need an eta conversion to adjust for the difference in arity.
          // (T0 a0, T1 a1, ...) => obj.F(additionalCustomParameter, a0, a1, ...)
          var callArguments = wr.ForkInParens();
          var sep = "";
          EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member, false), fn.tok, callArguments, ref sep);
          if (additionalCustomParameter != null) {
            callArguments.Write($"{sep}{additionalCustomParameter}");
            sep = ", ";
          }
          var lambdaHeader = new ConcreteSyntaxTree();
          var prefixSep = "";
          var arguments = lambdaHeader.ForkInParens();
          lambdaHeader.Write(" => ");
          
          foreach (var arg in fn.Formals) {
            if (!arg.IsGhost) {
              var name = idGenerator.FreshId("_eta");
              var ty = Resolver.SubstType(arg.Type, typeMap);
              arguments.Write($"{prefixSep}{TypeName(ty, arguments, arg.tok)} {name}");
              callArguments.Write($"{sep}{name}");
              sep = ", ";
              prefixSep = ", ";
            }
          }
          return EnclosedLvalue(lambdaHeader.ToString(), obj, $".{wr}");
        }
      } else {
        Contract.Assert(member is Field);
        if (member.IsStatic) {
          return SimpleLvalue(w => {
            w.Write("{0}.{1}", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            var sep = "(";
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member, false), member.tok, w, ref sep);
            if (sep != "(") {
              w.Write(")");
            }
          });
        } else if (NeedsCustomReceiver(member) && !(member.EnclosingClass is TraitDecl)) {
          // instance const in a newtype
          Contract.Assert(typeArgs.Count == 0);
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
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member, false), member.tok, w, ref sep);
            if (sep != "(") {
              w.Write(")");
            }
          });
        }
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      wr.Write("[");
      var sep = "";
      foreach (var index in indices) {
        wr.Write("{0}(int)({1})", sep, index);
        sep = ", ";
      }
      wr.Write("]");
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, ConcreteSyntaxTree wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      wr.Write("[");
      var sep = "";
      foreach (var index in indices) {
        wr.Write("{0}(int)", sep);
        TrParenExpr(index, wr, inLetExprBody);
        sep = ", ";
      }
      wr.Write("]");
      return w;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      TrParenExpr("(int)", expr, wr, inLetExprBody);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var xType = source.Type.NormalizeExpand();
      if (xType is MapType) {
        var inner = wr.Write(TypeHelperName(xType, wr, source.tok) + ".Select").ForkInParens();
        TrExpr(source, inner, inLetExprBody);
        inner.Write(",");
        TrExpr(index, inner, inLetExprBody);
      } else {
        TrParenExpr(source, wr, inLetExprBody);
        TrParenExpr(".Select", index, wr, inLetExprBody);
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var xType = source.Type.NormalizeExpand();
      if (xType is SeqType || xType is MapType) {
        wr.Write(TypeHelperName(xType, wr, source.tok) + ".Update");
        wr.Append(ParensList(
          Expr(source, inLetExprBody), 
          Expr(index, inLetExprBody), 
          Expr(value, inLetExprBody)));
      } else {
        TrParenExpr(source, wr, inLetExprBody);
        wr.Write(".Update");
        wr.Append(ParensList(
          Expr(index, inLetExprBody), 
          Expr(value, inLetExprBody)));
      }
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (fromArray) {
        wr.Write($"{DafnyHelpersClass}.SeqFromArray");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (hi != null) {
        if (lo != null) {
          wr.Write(".Subsequence");
          wr.Append(ParensList(Expr(lo, inLetExprBody), Expr(hi, inLetExprBody)));
        } else {
          TrParenExpr(".Take", hi, wr, inLetExprBody);
        }
      } else {
        if (lo != null) {
          TrParenExpr(".Drop", lo, wr, inLetExprBody);
        }
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (expr.Initializer is LambdaExpr lam) {
        Contract.Assert(lam.BoundVars.Count == 1);
        EmitSeqConstructionExprFromLambda(expr.N, lam.BoundVars[0], lam.Body, inLetExprBody, wr);
      } else {
        wr.Write("{0}<{1}>.Create", DafnyISeq, TypeName(expr.Type.AsSeqType.Arg, wr, expr.tok));
        wr.Append(ParensList(Expr(expr.N, inLetExprBody), Expr(expr.Initializer, inLetExprBody)));
      }
    }

    // Construct a sequence for the Dafny expression seq(N, F) in the common
    // case that f is a lambda expression.  In that case, rather than
    // something like
    //
    //   var s = Dafny.Sequence.Create(N, i => ...);
    //
    // (which will call the lambda N times), we'd rather write
    //
    //   var dim = N;
    //   var arr = new T[dim];
    //   for (int i = 0; i < dim; i++) {
    //     arr[i] = ...;
    //   }
    //   var s = Dafny.Sequence<T>.FromArray(a);
    //
    // and thus avoid method calls.  Unfortunately, since we can't add
    // statements easily, we have to settle for the slightly clunkier
    //
    //   var s = ((System.Func<Dafny.Sequence<T>>) (() => {
    //     var dim = N;
    //     var arr = new T[dim];
    //     for (int i = 0; i < dim; i++) {
    //       arr[i] = ...;
    //     }
    //     return Dafny.Sequence<T>.FromArray(a);
    //   }))();
    private void EmitSeqConstructionExprFromLambda(Expression lengthExpr, BoundVar boundVar, Expression body, bool inLetExprBody, ConcreteSyntaxTree wr) {
      wr.Format($"((System.Func<{TypeName(new SeqType(body.Type), wr, body.tok)}>) (() =>{ExprBlock(out ConcreteSyntaxTree wrLamBody)}))()");

      var indexType = lengthExpr.Type;
      var lengthVar = FreshId("dim");
      DeclareLocalVar(lengthVar, indexType, lengthExpr.tok, lengthExpr, inLetExprBody, wrLamBody);
      var arrVar = FreshId("arr");
      wrLamBody.Write($"var {arrVar} = ");
      var wrDims = EmitNewArray(body.Type, body.tok, dimCount: 1, mustInitialize: false, wr: wrLamBody);
      Contract.Assert(wrDims.Count == 1);
      wrDims[0].Write(lengthVar);
      wrLamBody.WriteLine(";");

      var intIxVar = FreshId("i");
      var wrLoopBody = wrLamBody.NewBlock(string.Format("for (int {0} = 0; {0} < {1}; {0}++)", intIxVar, lengthVar));
      var ixVar = IdName(boundVar);
      wrLoopBody.WriteLine("var {0} = ({1}) {2};",
        ixVar, TypeName(indexType, wrLoopBody, body.tok), intIxVar);
      var wrArrName = EmitArrayUpdate(new List<string> { ixVar }, body, wrLoopBody);
      wrArrName.Write(arrVar);
      wrLoopBody.WriteLine(";");

      wrLamBody.WriteLine("return {0}<{1}>.FromArray({2});", DafnySeqClass, TypeName(body.Type, wr, body.tok), arrVar);
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      wr.Write("{0}<{1}>", DafnyMultiSetClass, TypeName(expr.E.Type.AsCollectionType.Arg, wr, expr.tok));
      var eeType = expr.E.Type.NormalizeExpand();
      if (eeType is SeqType) {
        TrParenExpr(".FromSeq", expr.E, wr, inLetExprBody);
      } else if (eeType is SetType) {
        TrParenExpr(".FromSet", expr.E, wr, inLetExprBody);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr) {
      wr.Write($"{DafnyHelpersClass}.Id<{TypeName(functionType, wr, tok)}>({Expr(function, inLetExprBody)})");
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      from = from.NormalizeExpand();
      to = to.NormalizeExpand();
      Contract.Assert(from.IsRefType == to.IsRefType);

      var w = new ConcreteSyntaxTree();
      if (to.IsRefType) {
        wr.Format($"({TypeName(to, wr, tok)})({w})");
      } else {
        Contract.Assert(Type.SameHead(from, to));

        var wTypeArgs = to.TypeArgs.Comma(ta => TypeName(ta, wr, tok));
        var wConverters = from.TypeArgs.Zip(to.TypeArgs).Comma(t => DowncastConverter(t.First, t.Second, wr, tok));
        wr.Format($"({w}).DowncastClone<{wTypeArgs}>({wConverters})");
        Contract.Assert(from.TypeArgs.Count == to.TypeArgs.Count);
      }
      return w;
    }

    string DowncastConverter(Type from, Type to, ConcreteSyntaxTree errorWr, Bpl.IToken tok) {
      if (IsTargetSupertype(from, to, true)) {
        return $"Dafny.Helpers.Id<{TypeName(to, errorWr, tok)}>";
      }
      if (from.AsCollectionType != null) {
        var sTo = TypeName(to, errorWr, tok);
        // (from x) => { return x.DowncastClone<A, B, ...>(aConverter, bConverter, ...); }
        var wr = new ConcreteSyntaxTree();
        wr.Format($"({TypeName(@from, errorWr, tok)} x) => {{ return {Downcast(from, to, tok, (LineSegment)"x")}; }}");
        return wr.ToString();
      }
      // use a type
      return $"Dafny.Helpers.CastConverter<{TypeName(from, errorWr, tok)}, {TypeName(to, errorWr, tok)}>";
    }

    protected override bool TargetLambdaCanUseEnclosingLocals => false;

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments, List<Type> boundTypes, Type resultType, Bpl.IToken tok, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var tas = Util.Snoc(boundTypes, resultType);
      var typeArgs = TypeName_UDT(ArrowType.Arrow_FullCompileName, tas.ConvertAll(_ => TypeParameter.TPVariance.Non), tas, wr, tok);
      var result = new ConcreteSyntaxTree();
      wr.Format($"{DafnyHelpersClass}.Id<{typeArgs}>(({boundVars.Comma()}) => {result})");
      TrExprList(arguments, wr, inLetExprBody);
      return result;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      var dtorName = FormalName(dtor, formalNonGhostIndex);
      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source, ctor.EnclosingDatatype is CoDatatypeDecl ? "._Get()" : "", dtorName);
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, ConcreteSyntaxTree wr, bool untyped = false) {
      // (
      //   (System.Func<inTypes,resultType>)  // cast, which tells C# what the various types involved are
      //   (
      //     (inNames) => {
      //       <<caller fills in body here; must end with a return statement>>
      //     }
      //   )
      // )
      wr = wr.ForkInParens();
      if (!untyped) {
        wr.Write($"(System.Func<{inTypes.Concat(new [] {resultType}).Comma(t => TypeName(t, wr, tok))}>)");
      }
      wr.Format($"(({inNames.Comma(nm => nm)}) =>{ExprBlock(out ConcreteSyntaxTree body)})");
      return body;
    }

    protected override void CreateIIFE(string bvName, Type bvType, Bpl.IToken bvTok, Type bodyType, Bpl.IToken bodyTok, ConcreteSyntaxTree wr, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wrRhs = new ConcreteSyntaxTree();
      wrBody = new ConcreteSyntaxTree();
      wr.Format($"{DafnyHelpersClass}.Let<{TypeName(bvType, wr, bvTok)}, {TypeName(bodyType, wr, bodyTok)}>({wrRhs}, {bvName} => {wrBody})");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, Bpl.IToken resultTok, ConcreteSyntaxTree wr) {
      // (
      //   (System.Func<resultType>)(() => <<body>>)
      // )()
      wr.Format($"((System.Func<{TypeName(resultType, wr, resultTok)}>)(() =>{ExprBlock(out ConcreteSyntaxTree result)}))()");
      return result;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, ConcreteSyntaxTree wr) {
      wr.Format($"{DafnyHelpersClass}.Let<int, {TypeName(resultType, wr, resultTok)}>({source}, {bvName} => {Block(out ConcreteSyntaxTree result)})");
      return result;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr("new BigInteger(", expr, wr, inLetExprBody);
          wr.Write(".Count)");
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    static bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || t.IsIntegerType || t.IsRealType || t.AsNewtype != null || t.IsBitVectorType || t.IsBigOrdinalType || t.IsRefType;
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
        case BinaryExpr.ResolvedOpcode.EqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (e0.Type.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "== (object)";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "==";
            } else {
              staticCallString = "object.Equals";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
            } else if (e0.Type.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "!= (object)";
            } else if (IsDirectlyComparable(e0.Type)) {
              opString = "!=";
            } else {
              preOpString = "!";
              staticCallString = "object.Equals";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<"; truncateResult = true; convertE1_to_int = true; break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>"; convertE1_to_int = true; break;
        case BinaryExpr.ResolvedOpcode.Add:
          opString = "+"; truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char)(";
            postOpString = ")";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          opString = "-"; truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char)(";
            postOpString = ")";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*"; truncateResult = true; break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyHelpersClass}.EuclideanDivision{suffix}";
          } else {
            opString = "/";  // for reals
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyHelpersClass}.EuclideanModulus{suffix}";
          } else {
            opString = "%";  // for reals
          }
          break;

        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "Equals"; break;

        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          staticCallString = TypeHelperName(e0.Type, errorWr, tok, e1.Type) + ".IsProperSubsetOf"; break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          staticCallString = TypeHelperName(e0.Type, errorWr, tok, e1.Type) + ".IsSubsetOf"; break;

        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          staticCallString = TypeHelperName(e0.Type, errorWr, tok, e1.Type) + ".IsDisjointFrom"; break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "Contains"; reverseArguments = true; break;

        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          staticCallString = TypeHelperName(resultType, errorWr, tok) + ".Union"; break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          staticCallString = TypeHelperName(resultType, errorWr, tok) + ".Merge"; break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          staticCallString = TypeHelperName(resultType, errorWr, tok) + ".Intersect"; break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          staticCallString = TypeHelperName(resultType, errorWr, tok) + ".Difference"; break;

        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          staticCallString = TypeHelperName(resultType, errorWr, tok) + ".Subtract"; break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          staticCallString = TypeHelperName(e0.Type, errorWr, e0.tok) + ".IsProperPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          staticCallString = TypeHelperName(e0.Type, errorWr, e0.tok) + ".IsPrefixOf"; break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = TypeHelperName(e0.Type, errorWr, e0.tok) + ".Concat"; break;
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
      wr.Write("{0} == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("new Dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("new BigInteger");
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(", BigInteger.One)");
        } else if (e.ToType.IsCharType) {
          wr.Format($"(char)({Expr(e.E, inLetExprBody)})");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative == null && toNative == null) {
            if (e.E.Type.IsCharType) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("new BigInteger");
              TrParenExpr(e.E, wr, inLetExprBody);
            } else {
              // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
              TrExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("new BigInteger");
            TrParenExpr(e.E, wr, inLetExprBody);
          } else {
            bool toNativeNeedsCast;
            GetNativeInfo(toNative.Sel, out string toNativeName, out string toNativeSuffix, out toNativeNeedsCast);
            // any (int or bv) -> native (int or bv)
            // A cast would do, but we also consider some optimizations
            wr.Write("({0})", toNativeName);

            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("(" + literal + toNativeSuffix + ")");
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize .Count to avoid intermediate BigInteger
              TrParenExpr(u.E, wr, inLetExprBody);
              if (toNative.UpperBound <= new BigInteger(0x80000000U)) {
                wr.Write(".Count");
              } else {
                wr.Write(".LongCount");
              }
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              TrParenExpr(m.Obj, wr, inLetExprBody);
              if (toNative.UpperBound <= new BigInteger(0x80000000U)) {
                wr.Write(".Length");
              } else {
                wr.Write(".LongLength");
              }
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody);
            }
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else {
          // real -> (int or bv or char or ordinal)
          if (e.ToType.IsCharType) {
            wr.Write("(char)");
          } else if (AsNativeType(e.ToType) != null) {
            wr.Write("({0})", GetNativeTypeName(AsNativeType(e.ToType)));
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".ToBigInteger()");
        }
      } else if (e.E.Type.IsBigOrdinalType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int) || e.ToType.IsBigOrdinalType) {
          TrExpr(e.E, wr, inLetExprBody);
        } else if (e.ToType.IsCharType) {
          wr.Write("(char)");
          TrParenExpr(e.E, wr, inLetExprBody);
        } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          wr.Write("new Dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("new BigInteger");
            TrParenExpr(e.E, wr, inLetExprBody);
            wr.Write(", BigInteger.One)");
          } else {
            TrParenExpr(e.E, wr, inLetExprBody);
            wr.Write(", 1)");
          }
        } else if (e.ToType.IsBitVectorType) {
          // ordinal -> bv
          var typename = TypeName(e.ToType, wr, null, null);
          wr.Write($"({typename})");
          TrParenExpr(e.E, wr, inLetExprBody);
        } else {
          Contract.Assert(false, $"not implemented for C#: {e.E.Type} -> {e.ToType}");
        }
      } else {
        Contract.Assert(false, $"not implemented for C#: {e.E.Type} -> {e.ToType}");
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, Bpl.IToken tok, ConcreteSyntaxTree wr) {
      Contract.Requires(fromType.IsRefType);
      Contract.Requires(toType.IsRefType);

      // from T to U:   t is U && ...
      // from T to U?:  t is U && ...                 // since t is known to be non-null, this is fine
      // from T? to U:  t is U && ...                 // note, "is" implies non-null, so no need for explicit null check
      // from T? to U?: t == null || (t is U && ...)
      if (!fromType.IsNonNullRefType && !toType.IsNonNullRefType) {
        wr = wr.Write($"{localName} == null || ").ForkInParens();
      }

      var toClass = toType.NormalizeExpand();
      wr.Write($"{localName} is {TypeName(toClass, wr, tok)}");

      localName = $"(({TypeName(toClass, wr, tok)}){localName})";
      var udtTo = (UserDefinedType)toType.NormalizeExpandKeepConstraints();
      if (udtTo.ResolvedClass is SubsetTypeDecl && !(udtTo.ResolvedClass is NonNullTypeDecl)) {
        // TODO: test constraints
        throw new NotImplementedException();
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, ConcreteSyntaxTree wr) {
      wr.Write("{0}.FromElements", TypeHelperName(ct, wr, tok));
      TrExprList(elements, wr, inLetExprBody);
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var arguments = elements.Select(p =>
      {
        var result = new ConcreteSyntaxTree();
        result.Format($"new Dafny.Pair{BracketList((LineSegment)TypeName(p.A.Type, result, p.A.tok), (LineSegment)TypeName(p.B.Type, result, p.B.tok))}");
        result.Append(ParensList(Expr(p.A, inLetExprBody), Expr(p.B, inLetExprBody)));
        return result;
      }).ToArray<ICanRender>();
      wr.Write($"{TypeHelperName(mt, wr, tok)}.FromElements{ParensList(arguments)}");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      wrVarInit.Write("new System.Collections.Generic.List<{0}>()", TypeName(e.Type.AsSetType.Arg, wrVarInit, e.tok));
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      var wrVarInit = DeclareLocalVar(collectionName, null, null, wr);
      var mt = e.Type.AsMapType;
      var domtypeName = TypeName(mt.Domain, wrVarInit, e.tok);
      var rantypeName = TypeName(mt.Range, wrVarInit, e.tok);
      wrVarInit.Write($"new System.Collections.Generic.List<Dafny.Pair<{domtypeName},{rantypeName}>>()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (ct is SetType) {
        wr.FormatLine($"{collName}.Add({Expr(elmt, inLetExprBody)});");
      } else {
        Contract.Assume(false);  // unexpected collection type
      }
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var domtypeName = TypeName(mt.Domain, wr, tok);
      var rantypeName = TypeName(mt.Range, wr, tok);
      var termLeftWriter = new ConcreteSyntaxTree();
      wr.FormatLine($"{collName}.Add(new Dafny.Pair<{domtypeName},{rantypeName}>{ParensList(termLeftWriter, Expr(term, inLetExprBody))});");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, ConcreteSyntaxTree wr) {
      if (ct is SetType) {
        var typeName = TypeName(ct.Arg, wr, tok);
        return string.Format($"{DafnySetClass}<{typeName}>.FromCollection({collName})");
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
        return $"{DafnyMapClass}<{domtypeName},{rantypeName}>.FromCollection({collName})";
      } else {
        Contract.Assume(false);  // unexpected collection type
        throw new cce.UnreachableException();  // please compiler
      }
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr) {
      wr.Write($"{DafnyHelpersClass}.SingleValue<{type}>");
      TrParenExpr(e, wr, inLetExprBody);
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    private class CSharpCompilationResult
    {
      public Assembly CompiledAssembly;
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {

      compilationResult = null;

      // .NET Core does not allow C# compilation on all platforms using System.CodeDom. You need to use Roslyn libraries. Context: https://github.com/dotnet/runtime/issues/18768
      var compilation = CSharpCompilation.Create(Path.GetFileNameWithoutExtension(dafnyProgramName))
        .WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
        .AddReferences(
          MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location),
          MetadataReference.CreateFromFile(Assembly.Load("mscorlib").Location));

      var inMemory = runAfterCompile;
      compilation = compilation.WithOptions(compilation.Options.WithOutputKind(callToMain != null ? OutputKind.ConsoleApplication : OutputKind.DynamicallyLinkedLibrary));

      var tempCompilationResult = new CSharpCompilationResult();
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      if (DafnyOptions.O.UseRuntimeLib) {
        compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Path.Join(libPath, "DafnyRuntime.dll")));
      }

      var standardLibraries = new List<string>() {
        "System.Runtime",
        "System.Runtime.Numerics",
        "System.Collections",
        "System.Collections.Immutable",
        "System.Console"
      };
      compilation = compilation.AddReferences(standardLibraries.Select(fileName => MetadataReference.CreateFromFile(Assembly.Load(fileName).Location)));

      if (DafnyOptions.O.Optimize) {
        compilation = compilation.WithOptions(compilation.Options.WithOptimizationLevel(
          DafnyOptions.O.Optimize ? OptimizationLevel.Release : OptimizationLevel.Debug));
      }

      var otherSourceFiles = new List<string>();
      foreach (var file in otherFileNames) {
        string extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }
        if (extension == ".cs") {
          var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
          if (File.Exists(normalizedPath)) {
            otherSourceFiles.Add(normalizedPath);
          } else {
            outputWriter.WriteLine("Errors compiling program: Could not find {0}", file);
            return false;
          }
        } else if (extension == ".dll") {
          compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Path.GetFullPath(file)));
        }
      }

      var source = callToMain == null ? targetProgramText : targetProgramText + callToMain;
      compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(source));
      foreach (var sourceFile in otherSourceFiles) {
        compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(File.ReadAllText(sourceFile)));
      }
      var outputDir = targetFilename == null ? Directory.GetCurrentDirectory() : Path.GetDirectoryName(Path.GetFullPath(targetFilename));
      var outputPath = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".dll");
      var outputJson = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".runtimeconfig.json");
      if (inMemory) {
        using var stream = new MemoryStream();
        var emitResult = compilation.Emit(stream);
        if (emitResult.Success) {
          tempCompilationResult.CompiledAssembly = Assembly.Load(stream.GetBuffer());
        } else {
          outputWriter.WriteLine("Errors compiling program:");
          var errors = emitResult.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
          foreach (var ce in errors) {
            outputWriter.WriteLine(ce.ToString());
            outputWriter.WriteLine();
          }
          return false;
        }
      } else {
        var emitResult = compilation.Emit(outputPath);

        if (emitResult.Success) {
          tempCompilationResult.CompiledAssembly = Assembly.LoadFile(outputPath);
          if (DafnyOptions.O.CompileVerbose) {
            outputWriter.WriteLine("Compiled assembly into {0}.dll", compilation.AssemblyName);
          }
          try {
            var configuration = JsonSerializer.Serialize(
              new {
                runtimeOptions = new {
                  tfm = "net5.0",
                  framework = new {
                    name = "Microsoft.NETCore.App",
                    version = "5.0.0",
                    rollForward = "LatestMinor"
                  }
                }
              }, new JsonSerializerOptions() { WriteIndented = true });
            File.WriteAllText(outputJson, configuration + Environment.NewLine);
          } catch (Exception e) {
            outputWriter.WriteLine($"Error trying to write '{outputJson}': {e.Message}");
            return false;
          }
        } else {
          outputWriter.WriteLine("Errors compiling program into {0}", compilation.AssemblyName);
          var errors = emitResult.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
          foreach (var ce in errors) {
            outputWriter.WriteLine(ce.ToString());
            outputWriter.WriteLine();
          }
          return false;
        }
      }

      compilationResult = tempCompilationResult;
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      var crx = (CSharpCompilationResult)compilationResult;

      foreach (var otherFileName in otherFileNames) {
        if (Path.GetExtension(otherFileName) == ".dll") {
          AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.GetFullPath(otherFileName));
        }
      }

      if (crx.CompiledAssembly == null) {
        throw new Exception("Cannot call run target program on a compilation that failed");
      }
      var entry = crx.CompiledAssembly.EntryPoint;
      if (entry == null) {
        throw new Exception("Cannot call run target on a compilation whose assembly has no entry.");
      }
      try {
        object[] parameters = entry.GetParameters().Length == 0 ? new object[] { } : new object[] { new string[0] };
        entry.Invoke(null, parameters);
        return true;
      } catch (System.Reflection.TargetInvocationException e) {
        outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
        outputWriter.WriteLine(e.InnerException.ToString());
      } catch (System.Exception e) {
        outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
        outputWriter.WriteLine(e.ToString());
      }
      return false;
    }

    private void AddTestCheckerIfNeeded(string name, Declaration decl, ConcreteSyntaxTree wr) {
      if (Attributes.Contains(decl.Attributes, "test")) {
        // TODO: The resolver needs to check the assumptions about the declaration
        // (i.e. must be public and static, must return a "result type", etc.)
        bool hasReturnValue = false;
        if (decl is Function) {
          hasReturnValue = true;
        } else if (decl is Method) {
          var method = (Method)decl;
          hasReturnValue = method.Outs.Count > 1;
        }

        wr.WriteLine("[Xunit.Fact]");
        if (hasReturnValue) {
          wr = wr.NewNamedBlock("public static void {0}_CheckForFailureForXunit()", name);
          wr.WriteLine("var result = {0}();", name);
          wr.WriteLine("Xunit.Assert.False(result.IsFailure(), \"Dafny test failed: \" + result);");
        }
      }
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), wr, mainMethod.tok, mainMethod);
      var wClass = wr.NewNamedBlock("class __CallToMain");
      var wBody = wClass.NewNamedBlock("public static void Main(string[] args)");
      var modName = mainMethod.EnclosingClass.EnclosingModuleDefinition.CompileName == "_module" ? "_module." : "";
      companion = modName + companion;

      var idName = IssueCreateStaticMain(mainMethod) ? "_StaticMain" : IdName(mainMethod);

      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{GetHelperModuleName()}.WithHaltHandling({companion}.{idName});");
      Coverage.EmitTearDown(wBody);
    }
  }
}
