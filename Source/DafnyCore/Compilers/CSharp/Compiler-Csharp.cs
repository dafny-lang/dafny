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
using Microsoft.CodeAnalysis.CSharp;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using static Microsoft.Dafny.ConcreteSyntaxTreeUtils;

namespace Microsoft.Dafny.Compilers {
  public class CsharpCompiler : SinglePassCompiler {
    protected bool Synthesize = false;

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.SubsetTypeTests,
      Feature.TuplesWiderThan20
    };

    public CsharpCompiler(ErrorReporter reporter) : base(reporter) {
    }

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
      wr.WriteLine("// but the 'dotnet' tool in net6.0 should pick those up automatically.");
      wr.WriteLine("// Optionally, you may want to include compiler switches like");
      wr.WriteLine("//     /debug /nowarn:162,164,168,183,219,436,1717,1718");
      wr.WriteLine();
      wr.WriteLine("using System;");
      wr.WriteLine("using System.Numerics;");
      wr.WriteLine("using System.Collections;");
      Synthesize = ProgramHasMethodsWithAttr(program, "synthesize");
      if (Synthesize) {
        CsharpSynthesizer.EmitImports(wr);
      }
      EmitDafnySourceAttribute(program, wr);
      ReadRuntimeSystem(program, "DafnyRuntime.cs", wr);
    }

    /// <summary>
    /// Return true if the AST contains a method annotated with an attribute
    /// </summary>
    private static bool ProgramHasMethodsWithAttr(Program p, String attr) {
      foreach (var module in p.Modules()) {
        foreach (ICallable callable in ModuleDefinition.AllCallables(
                   module.TopLevelDecls)) {
          if ((callable is Method method) &&
              Attributes.Contains(method.Attributes, attr)) {
            return true;
          }
        }
      }
      return false;
    }

    void EmitDafnySourceAttribute(Program program, ConcreteSyntaxTree wr) {
      Contract.Requires(program != null);
      Contract.Requires(wr != null);

      var strwr = new StringWriter();
      strwr.NewLine = Environment.NewLine;
      new Printer(strwr, PrintModes.DllEmbed).PrintProgram(program, true);
      var programString = strwr.GetStringBuilder().Replace("\"", "\"\"").ToString();

      wr.WriteLine($"[assembly: DafnyAssembly.DafnySourceAttribute(@\"{programString}\")]");
      wr.WriteLine();
    }

    protected override void EmitBuiltInDecls(BuiltIns builtIns, ConcreteSyntaxTree wr) {
      if (builtIns.MaxNonGhostTupleSizeUsed > 20) {
        UnsupportedFeatureError(builtIns.MaxNonGhostTupleSizeToken, Feature.TuplesWiderThan20);
      }

      var dafnyNamespace = CreateModule("Dafny", false, false, null, wr);
      EmitInitNewArrays(builtIns, dafnyNamespace);
      if (Synthesize) {
        CsharpSynthesizer.EmitMultiMatcher(dafnyNamespace);
      }
      EmitFuncExtensions(builtIns, wr);
    }

    // Generates casts for functions of those arities present in the program, like:
    //   public static class FuncExtensions {
    //     public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F,
    //         Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    //       return arg => ResConv(F(ArgConv(arg)));
    //     }
    //     ...
    //   }
    // They aren't in any namespace to make them universally accessible.
    private void EmitFuncExtensions(BuiltIns builtIns, ConcreteSyntaxTree wr) {
      var funcExtensions = wr.NewNamedBlock("internal static class FuncExtensions");
      foreach (var kv in builtIns.ArrowTypeDecls) {
        int arity = kv.Key;

        List<string> TypeParameterList(string prefix) {
          var l = arity switch {
            1 => new List<string> { prefix },
            _ => Enumerable.Range(1, arity).Select(i => $"{prefix}{i}").ToList()
          };
          l.Add($"{prefix}Result");
          return l;
        }

        var us = TypeParameterList("U");
        var ts = TypeParameterList("T");

        string ArgConvDecl((string u, string t) tp) => $"Func<{tp.u}, {tp.t}> ArgConv";
        var argConvDecls = arity switch {
          0 => "",
          1 => $"{ArgConvDecl(("U", "T"))}, ",
          _ => us.SkipLast(1).Zip(ts.SkipLast(1))
                 .Comma((tp, i) => $"{ArgConvDecl(tp)}{++i}")
               + ", "
        };

        var parameters = $"this Func<{ts.Comma()}> F, {argConvDecls}Func<TResult, UResult> ResConv";
        funcExtensions.Write($"public static Func<{us.Comma()}> DowncastClone<{ts.Concat(us).Comma()}>({parameters})");

        var binder = arity switch { 1 => "arg", _ => $"({Enumerable.Range(1, arity).Comma(i => $"arg{i}")})" };
        var argConvCalls = arity switch {
          1 => "ArgConv(arg)",
          _ => Enumerable.Range(1, arity).Comma(i => $"ArgConv{i}(arg{i})")
        };
        funcExtensions.NewBlock().WriteLine($"return {binder} => ResConv(F({argConvCalls}));");
      }
    }

    private void EmitInitNewArrays(BuiltIns builtIns, ConcreteSyntaxTree dafnyNamespace) {
      var arrayHelpers = dafnyNamespace.NewNamedBlock("internal class ArrayHelpers");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl classDecl) {
          int dims = classDecl.Dims;

          // Here is an overloading of the method name, where there is an initialValue parameter
          // public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
          arrayHelpers.Write(
            $"public static T[{Repeat("", dims, ",")}] InitNewArray{dims}<T>(T z, {Repeat("BigInteger size{0}", dims, ", ")})");

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

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var wr = ((ClassWriter)cw).StaticMemberWriter;
      // See EmitCallToMain() - this is named differently because otherwise C# tries
      // to resolve the reference to the instance-level Main method
      return wr.NewBlock($"public static void _StaticMain(Dafny.ISequence<Dafny.ISequence<{CharTypeName}>> {argsParameterName})");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, ConcreteSyntaxTree wr) {
      return wr.NewBlock($"namespace {IdProtect(moduleName)}", " // end of " + $"namespace {IdProtect(moduleName)}");
    }

    protected override string GetHelperModuleName() => DafnyHelpersClass;

    const string DafnyTypeDescriptor = "Dafny.TypeDescriptor";

    internal string TypeParameters(List<TypeParameter>/*?*/ targs, bool addVariance = false, bool uniqueNames = false) {
      Contract.Requires(targs == null || cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      if (targs == null || targs.Count == 0) {
        return "";
      }

      string PrintVariance(TypeParameter.TPVariance variance) {
        if (addVariance) {
          switch (variance) {
            case TypeParameter.TPVariance.Co:
              return "out ";
            case TypeParameter.TPVariance.Contra:
              return "in ";
          }
        }
        return "";
      }

      string PrintTypeParameter(TypeParameter tArg) => $"{PrintVariance(tArg.Variance)}{(uniqueNames ? "__" : "")}{IdName(tArg)}";

      return $"<{targs.Comma(PrintTypeParameter)}>";
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
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
      var initializer = DefaultValue(type, wr, enclosingTypeDecl.tok, true);

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

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TopLevelDecl trait, List<Type> superClasses /*?*/, IToken tok, ConcreteSyntaxTree wr) {
      var instanceMemberWriter = WriteTypeHeader("interface", name, typeParameters, superClasses, tok, wr);

      //writing the _Companion class
      wr.Write($"public class _Companion_{name}{TypeParameters(typeParameters)}");
      var staticMemberWriter = wr.NewBlock();

      return new ClassWriter(this, instanceMemberWriter, null, staticMemberWriter);
    }

    private ConcreteSyntaxTree WriteTypeHeader(string kind, string name, List<TypeParameter> typeParameters, List<Type>/*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
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

      var cw = (ClassWriter)CreateClass(IdProtect(iter.EnclosingModuleDefinition.CompileName), IdName(iter), iter, wr);
      var w = cw.InstanceMemberWriter;
      // here come the fields

      var constructors = iter.Members.OfType<Constructor>().ToList();

      // we're expecting just one constructor 
      var enumerable = constructors.ToList();
      Contract.Assert(enumerable.Count == 1);
      Constructor ct = constructors[0];

      foreach (var member in iter.Members) {
        if (member is Field f && !f.IsGhost) {
          cw.DeclareField(IdName(f), iter, false, false, f.Type, f.tok, PlaceboValue(f.Type, w, f.tok, true), f);
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

    private string DtTypeName(TopLevelDecl dt, bool typeVariables = true) {
      var name = "_I" + dt.CompileName;
      if (typeVariables) { name += TypeParameters(SelectNonGhost(dt, dt.TypeArgs)); }
      return name;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      var w = CompileDatatypeBase(dt, wr);
      CompileDatatypeConstructors(dt, wr);
      return w;
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      Contract.Requires(dt != null);
      Contract.Requires(wr != null);

      // public interface _IDt<T> { // T has variance modifier
      //   _IDt<T> _Get();  // for co-datatypes
      //
      //   bool is_Ctor0 { get; }
      //   ...
      //
      //   T0 dtor_Dtor0 { get; }
      //   ...
      //
      //   _IDt<U> DowncastClone<U>(Func<T0, U0> converter0, ...);
      //
      //   // Members that don't violate C# variance restrictions
      // }
      //
      // public abstract class Dt<T> : _IDt<T> {  // for record types: drop "abstract"
      //   public Dt() { }
      //   #if TypeArgs.Count == 0
      //     private static _IDt<T> theDefault = ...;
      //     public static _IDt<T> Default() {
      //       return theDefault;
      //     }
      //   #else
      //     public static _IDt<T> Default(values...) {
      //       return ...;
      //     }
      //   #endif
      //   public static TypeDescriptor<_IDt<T>> _TypeDescriptor(typeDescriptors...) {
      //     return new TypeDescriptor<_IDt<T>>(Default(typeDescriptors...));
      //   }
      //   public abstract _IDt<T> _Get();  // for co-datatypes
      //
      //   public static _IDt<T> create_Ctor0(field0, field1, ...) {  // for record types: create
      //     return new Dt_Ctor0(field0, field1, ...);                // for record types: new Dt
      //   }
      //   ...
      //
      //   public bool is_Ctor0 { get { return this is Dt_Ctor0; } }  // for record types: return true
      //   ...
      //
      //   // if the datatype HasFinitePossibleValues
      //   public static System.Collections.Generic.IEnumerable<_IDt<T>> AllSingletonConstructors { get {
      //     yield return _IDt<T>.create_Ctor0();
      //     ...
      //   }}
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
      //
      //   public abstract _IDt<U> DowncastClone<U>(Func<T0, U0> converter0, ...); // for record types: implementation
      //
      //   // Implementations of all members, but possibly (variance) rewritten to be static.
      // }
      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);
      var DtT_TypeArgs = TypeParameters(nonGhostTypeArgs);
      var DtT_protected = IdName(dt) + DtT_TypeArgs;
      var simplifiedType = DatatypeWrapperEraser.SimplifyType(UserDefinedType.FromTopLevelDecl(dt.tok, dt));
      var simplifiedTypeName = TypeName(simplifiedType, wr, dt.tok);

      // ContreteSyntaxTree for the interface
      var interfaceTree = wr.NewNamedBlock($"public interface _I{dt.CompileName}{TypeParameters(nonGhostTypeArgs, true)}");

      // from here on, write everything into the new block created here:
      var btw = wr.NewNamedBlock("public{0} class {1} : {2}", dt.IsRecordType ? "" : " abstract", DtT_protected, DtTypeName(dt));
      wr = btw;

      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine($"public {IdName(dt)}() {{ }}");
      }

      var wDefault = new ConcreteSyntaxTree();
      if (nonGhostTypeArgs.Count == 0) {
        wr.FormatLine($"private static readonly {simplifiedTypeName} theDefault = {wDefault};");
        var w = wr.NewBlock($"public static {simplifiedTypeName} Default()");
        w.WriteLine("return theDefault;");
      } else {
        var parameters = UsedTypeParameters(dt).Comma(tp => $"{tp.CompileName} {FormatDefaultTypeParameterValue(tp)}");
        wr.Write($"public static {simplifiedTypeName} Default({parameters})");
        var w = wr.NewBlock();
        w.FormatLine($"return {wDefault};");
      }

      var groundingCtor = dt.GetGroundingCtor();
      if (groundingCtor.IsGhost) {
        wDefault.Write(ForcePlaceboValue(simplifiedType, wDefault, dt.tok));
      } else if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(dt, out var innerType)) {
        wDefault.Write(DefaultValue(innerType, wDefault, dt.tok));
      } else {
        if (dt is CoDatatypeDecl) {
          var wCo = wDefault;
          wDefault = new ConcreteSyntaxTree();
          wCo.Format($"new {dt.FullCompileName}__Lazy{DtT_TypeArgs}(() => {{ return {wDefault}; }})");
        }

        wDefault.Write(DtCreateName(groundingCtor));
        var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost);
        wDefault.Write($"({nonGhostFormals.Comma(f => DefaultValue(f.Type, wDefault, f.tok))})");
      }

      EmitTypeDescriptorMethod(dt, wr);

      if (dt is CoDatatypeDecl) {
        interfaceTree.WriteLine($"{DtTypeName(dt)} _Get();");
        wr.WriteLine($"public abstract {DtTypeName(dt)} _Get();");
      }

      // create methods
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        wr.Write($"public static {DtTypeName(dt)} {DtCreateName(ctor)}(");
        WriteFormals("", ctor.Formals, wr);
        var w = wr.NewBlock(")");
        var arguments = ctor.Formals.Where(f => !f.IsGhost).Comma(FormalName);
        w.WriteLine($"return new {DtCtorDeclarationName(ctor)}{DtT_TypeArgs}({arguments});");
      }

      // query properties
      if (dt is TupleTypeDecl) {
        // omit the is_ property for tuples, since it cannot be used syntactically in the language
      } else {
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          interfaceTree.WriteLine($"bool is_{ctor.CompileName} {{ get; }}");

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
          $"public static System.Collections.Generic.IEnumerable<{DtTypeName(dt)}> AllSingletonConstructors");
        var wGet = w.NewBlock("get");
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          var constructor = ctor.IsGhost
            ? ForcePlaceboValue(UserDefinedType.FromTopLevelDecl(dt.tok, dt), wGet, dt.tok)
            : $"{DtT_protected}.{DtCreateName(ctor)}()";
          wGet.WriteLine($"yield return {constructor};");
        }
      }

      CompileDatatypeDestructorsAndAddToInterface(dt, wr, interfaceTree, DtT_TypeArgs);

      CompileDatatypeDowncastClone(dt, interfaceTree, nonGhostTypeArgs, toInterface: true);
      if (!dt.IsRecordType) {
        CompileDatatypeDowncastClone(dt, wr, nonGhostTypeArgs);
      }

      CompileDatatypeInterfaceMembers(dt, interfaceTree);

      return new ClassWriter(this, btw, null);
    }

    /// <summary>
    /// Generate the "DowncastClone" code for a generated datatype. This includes the exported signature for the interface,
    /// the abstract method for the abstract class, and the actual implementations for the constructor classes. If the
    /// datatype is a record type, there is no abstract class, so the method is directly emitted. Contravariant type
    /// parameters require a CustomReceiver-like treatment involving static methods and can thus require a jump table in
    /// the abstract class. Erasable type wrappers require the same kind of CustomReceiver-like treatment and operate
    /// on the unwrapped type.
    /// toInterface: just the signature for the interface
    /// lazy: convert the computer of a codatatype's "__Lazy" class
    /// ctor: constructor to generate the method for
    /// </summary>
    private void CompileDatatypeDowncastClone(DatatypeDecl datatype, ConcreteSyntaxTree wr,
        List<TypeParameter> nonGhostTypeArgs, bool toInterface = false, bool lazy = false, DatatypeCtor ctor = null) {
      bool InvalidType(Type ty, bool refTy) =>
        (ty.AsTypeParameter != null && refTy && datatype.TypeArgs.Contains(ty.AsTypeParameter))
        || ty.TypeArgs.Exists(arg => InvalidType(arg, refTy || ty.IsRefType));

      if (datatype.Ctors.Any(ctor => ctor.Formals.Any(f => !f.IsGhost && InvalidType(f.SyntacticType, false)))) {
        return;
      }

      var customReceiver = DowncastCloneNeedsCustomReceiver(datatype);
      var uTypeArgs = TypeParameters(nonGhostTypeArgs, uniqueNames: true);
      var typeArgs = TypeParameters(nonGhostTypeArgs);
      var typeSubstMap = nonGhostTypeArgs.ToDictionary(
        tp => tp,
        tp => (Type)new UserDefinedType(tp.tok, new TypeParameter(tp.RangeToken, tp.NameNode.Prepend("_"), tp.VarianceSyntax)));

      var resultType = DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(datatype, out var innerType)
        ? TypeName(innerType.Subst(typeSubstMap), wr, datatype.tok)
        : "_I" + datatype.CompileName + uTypeArgs;
      var converters = $"{nonGhostTypeArgs.Comma((_, i) => $"converter{i}")}";
      var lazyClass = $"{datatype.FullCompileName}__Lazy";
      string PrintConverter(TypeParameter tArg, int i) {
        var name = IdName(tArg);
        return $"Func<{name}, __{name}> converter{i}";
      }

      if (!toInterface) {
        string Modifiers(string abs, string single, string cons) =>
          (ctor != null || lazy) ? (datatype.IsRecordType ? single : cons) : abs;
        var modifiers = customReceiver
          ? Modifiers("static ", "static ", "new static ")
          : Modifiers("abstract ", "", "override ");
        wr.Write($"public {modifiers}");
      }

      if (!(toInterface && customReceiver)) {
        string receiver;
        if (customReceiver) {
          var simplifiedType = DatatypeWrapperEraser.SimplifyType(UserDefinedType.FromTopLevelDecl(datatype.tok, datatype));
          receiver = $"{TypeName(simplifiedType, wr, datatype.tok)} _this";
        } else {
          receiver = "";
        }
        var comma = receiver.Length != 0 && nonGhostTypeArgs.Count != 0 ? ", " : "";
        wr.Write($"{resultType} DowncastClone{uTypeArgs}({receiver}{comma}{nonGhostTypeArgs.Comma(PrintConverter)})");
      }

      if (ctor == null && !lazy) {
        if (!customReceiver) {
          wr.WriteLine(";");
        } else if (!toInterface) {
          var body = wr.NewBlock();

          ConcreteSyntaxTree NextBlock(string comp) { return body.NewBlock($"if (_this{comp})"); }

          void WriteReturn(ConcreteSyntaxTree wr, string staticClass) {
            var comma = converters.Length != 0 ? ", " : "";
            wr.WriteLine($"return {staticClass}{typeArgs}.DowncastClone{uTypeArgs}(_this{comma}{converters});");
          }

          if (datatype is CoDatatypeDecl) {
            WriteReturn(NextBlock($" is {lazyClass}{typeArgs}"), lazyClass);
          }

          var nonGhostConstructors = datatype.Ctors.Where(ctor => !ctor.IsGhost).ToList();
          for (var i = 0; i < nonGhostConstructors.Count; i++) {
            var ret = body;
            //The final constructor is chosen as the default
            if (i + 1 < nonGhostConstructors.Count) {
              ret = NextBlock($".is_{nonGhostConstructors[i].CompileName}");
            }
            WriteReturn(ret, DtCtorDeclarationName(nonGhostConstructors[i]));
          }
        }
        return;
      }

      string PrintConvertedExpr(string name, Type fromType) {
        var constructorIndex = nonGhostTypeArgs.IndexOf(fromType.AsTypeParameter);
        if (constructorIndex != -1) {
          return $"converter{constructorIndex}({name})";
        }

        bool ContainsTyVar(TypeParameter tp, Type ty)
          => (ty.AsTypeParameter != null && ty.AsTypeParameter.Equals(tp))
             || ty.TypeArgs.Exists(ty => ContainsTyVar(tp, ty));
        if (nonGhostTypeArgs.Exists(ty => ContainsTyVar(ty, fromType))) {
          var map = nonGhostTypeArgs.ToDictionary(
            tp => tp,
            tp => (Type)new UserDefinedType(tp.tok, new TypeParameter(tp.RangeToken, tp.NameNode.Prepend("_"), tp.VarianceSyntax)));
          var to = fromType.Subst(map);
          var downcast = new ConcreteSyntaxTree();
          EmitDowncast(fromType, to, null, downcast).Write(name);
          return downcast.ToString();
        }

        return name;
      }

      string PrintInvocation(Formal f, int i) {
        var name = customReceiver
          ? datatype.IsRecordType || !f.HasName
            ? $"(({DtCtorDeclarationName(ctor)}{typeArgs}) _this).{FieldName(f, i)}"
            : $"_this.{DestructorGetterName(f, ctor, i)}"
          : FieldName(f, i);
        return PrintConvertedExpr(name, f.Type);
      }

      if (innerType != null) {
        var wBody = wr.NewBlock("");
        wBody.WriteLine($"return {PrintConvertedExpr("_this", innerType)};");
      } else {
        var wBody = wr.NewBlock("").WriteLine($"if ({(customReceiver ? "_" : "")}this is {resultType} dt) {{ return dt; }}");
        var constructorArgs = lazy
          ? customReceiver
            ? $"() => {datatype.CompileName}{typeArgs}.DowncastClone{uTypeArgs}(_this._Get(), {converters})"
            : $"() => _Get().DowncastClone{uTypeArgs}({converters})"
          : ctor.Formals.Where(f => !f.IsGhost).Comma(PrintInvocation);

        var className = lazy ? lazyClass : DtCtorDeclarationName(ctor);
        wBody.WriteLine($"return new {className}{uTypeArgs}({constructorArgs});");
      }
    }

    // Emits getters for both named and unnamed destructors. The named ones are grouped across constructors by their
    // name and thus QDtorM = DtorM. This is not possible for unnamed ones, as there is no guarantee about shared return
    // types, so they are treated individually and their names (QDtorM) are qualified by their respective constructors.
    private void CompileDatatypeDestructorsAndAddToInterface(DatatypeDecl dt, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree interfaceTree, string DtT_TypeArgs) {
      foreach (var ctor in dt.Ctors) {
        var index = 0;
        foreach (var dtor in ctor.Destructors.Where(dtor => dtor.EnclosingCtors[0] == ctor)) {
          var compiledConstructorCount = dtor.EnclosingCtors.Count(constructor => !constructor.IsGhost);
          if (compiledConstructorCount != 0) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost) {
              var DtorM = arg.HasName ? "_" + arg.CompileName : FieldName(arg, index);
              //   TN dtor_QDtorM { get; }
              interfaceTree.WriteLine($"{TypeName(arg.Type, wr, arg.tok)} {DestructorGetterName(arg, ctor, index)} {{ get; }}");

              //   public TN dtor_QDtorM { get {
              //       var d = this;         // for inductive datatypes
              //       var d = this._Get();  // for co-inductive datatypes
              //       if (d is DT_Ctor0) { return ((DT_Ctor0)d).DtorM; }
              //       if (d is DT_Ctor1) { return ((DT_Ctor1)d).DtorM; }
              //       ...
              //       if (d is DT_Ctor(n-2)) { return ((DT_Ctor(n-2))d).DtorM; }
              //       return ((DT_Ctor(n-1))d).DtorM;
              //    }}
              var wDtor =
                wr.NewNamedBlock($"public {TypeName(arg.Type, wr, arg.tok)} {DestructorGetterName(arg, ctor, index)}");
              var wGet = wDtor.NewBlock("get");
              if (dt.IsRecordType) {
                if (dt is CoDatatypeDecl) {
                  wGet.WriteLine($"return this._Get().{IdProtect(DtorM)};");
                } else {
                  wGet.WriteLine($"return this.{IdProtect(DtorM)};");
                }
              } else {
                if (dt is CoDatatypeDecl) {
                  wGet.WriteLine("var d = this._Get();");
                } else {
                  wGet.WriteLine("var d = this;");
                }

                var compiledConstructorsProcessed = 0;
                for (var i = 0; i < dtor.EnclosingCtors.Count; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  if (ctor_i.IsGhost) {
                    continue;
                  }
                  var type = $"{dt.CompileName}_{ctor_i.CompileName}{DtT_TypeArgs}";
                  // TODO use pattern matching to replace cast.
                  var returnTheValue = $"return (({type})d).{IdProtect(DtorM)};";
                  if (compiledConstructorsProcessed < compiledConstructorCount - 1) {
                    wGet.WriteLine($"if (d is {type}) {{ {returnTheValue} }}");
                  } else {
                    wGet.WriteLine(returnTheValue);
                  }
                  compiledConstructorsProcessed++;
                }
              }
              index++;
            }
          }
        }
      }
    }

    private void CompileDatatypeInterfaceMembers(DatatypeDecl dt, ConcreteSyntaxTree interfaceTree) {
      foreach (var member in dt.Members) {
        if (member.IsGhost || member.IsStatic) { continue; }
        if (member is Function fn && !NeedsCustomReceiver(member)) {
          CreateFunction(IdName(fn), CombineAllTypeArguments(fn), fn.Formals, fn.ResultType, fn.tok, fn.IsStatic,
            false, fn, interfaceTree, false, false);
        } else if (member is Method m && !NeedsCustomReceiver(member)) {
          CreateMethod(m, CombineAllTypeArguments(m), false, interfaceTree, false, false);
        } else if (member is ConstantField c && !NeedsCustomReceiver(member)) {
          CreateFunctionOrGetter(c, IdName(c), dt, false, false, false, new ClassWriter(this, interfaceTree, null));
        }
      }
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

    public override bool NeedsCustomReceiver(MemberDecl member) {
      //Dafny and C# have different ideas about variance, so not every datatype member can be in the interface.
      if (!member.IsStatic && member.EnclosingClass is DatatypeDecl d) {
        foreach (var tp in d.TypeArgs) {
          bool InvalidType(Type ty) => (ty.AsTypeParameter != null && ty.AsTypeParameter.Equals(tp))
                                       || ty.TypeArgs.Exists(InvalidType);
          bool InvalidFormal(Formal f) => !f.IsGhost && InvalidType(f.SyntacticType);
          switch (tp.Variance) {
            //Can only be in output
            case TypeParameter.TPVariance.Co:
              if ((member is Function f && f.Formals.Exists(InvalidFormal))
                  || (member is Method m && m.Ins.Exists(InvalidFormal))) { return true; }
              break;
            //Can only be in input
            case TypeParameter.TPVariance.Contra:
              if ((member is Function fn && InvalidType(fn.ResultType))
                  || (member is Method me && me.Outs.Exists(InvalidFormal))
                  || (member is ConstantField c && InvalidType(c.Type))) { return true; }
              break;
          }
        }
      }

      return base.NeedsCustomReceiver(member);
    }


    private void CompileDatatypeConstructors(DatatypeDecl dt, ConcreteSyntaxTree wrx) {
      Contract.Requires(dt != null);
      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);
      string typeParams = TypeParameters(nonGhostTypeArgs);
      if (dt is CoDatatypeDecl) {
        // public class Dt__Lazy<T> : Dt<T> {
        //   public delegate _IDt<T> Computer();
        //   Computer c;
        //   _IDt<T> d;
        //   public Dt__Lazy(Computer c) { this.c = c; }
        //   public override _IDt<U> DowncastClone<U>(Func<T0, U0> converter0, ...) {
        //     if (this is _IDt<U> dt) { return dt; }
        //     return new Dt__Lazy<U>(() => c().DowncastClone<U>(converter0, ...));
        //   }
        //   public override _IDt<T> _Get() { if (c != null) { d = c(); c = null; } return d; }
        //   public override string ToString() { return _Get().ToString(); }
        // }
        var w = wrx.NewNamedBlock($"public class {dt.CompileName}__Lazy{typeParams} : {IdName(dt)}{typeParams}");
        w.WriteLine($"public {NeedsNew(dt, "Computer")}delegate {DtTypeName(dt)} Computer();");
        w.WriteLine($"{NeedsNew(dt, "c")}Computer c;");
        w.WriteLine($"{NeedsNew(dt, "d")}{DtTypeName(dt)} d;");
        w.WriteLine($"public {dt.CompileName}__Lazy(Computer c) {{ this.c = c; }}");
        CompileDatatypeDowncastClone(dt, w, nonGhostTypeArgs, lazy: true);
        w.WriteLine($"public override {DtTypeName(dt)} _Get() {{ if (c != null) {{ d = c(); c = null; }} return d; }}");
        w.WriteLine("public override string ToString() { return _Get().ToString(); }");
      }

      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }

      int constructorIndex = 0; // used to give each constructor a different name
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
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
      // class Dt_Ctor<T> : Dt<T> {  // This line is to be added by the caller of DatatypeFieldsAndConstructor
      //   Fields;
      //   public Dt_Ctor(arguments) {  // for record types: Dt
      //     Fields = arguments;
      //   }
      //   public override _IDt<T> _Get() { return this; }  // for co-datatypes only
      //   public override _IDt<U> DowncastClone<U>(Func<T0, U0> converter0, ...) {
      //     if (this is _IDt<U> dt) {
      //       return dt;
      //     } else {
      //       return new Dt_Ctor<U>(converter0(_field0), ...);
      //     }
      //   }
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
          wr.WriteLine($"public readonly {TypeName(arg.Type, wr, arg.tok)} {FieldName(arg, i)};");
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
            w.WriteLine($"this.{FieldName(arg, i)} = {FormalName(arg, i)};");
            i++;
          }
        }
      }

      var nonGhostTypeArgs = SelectNonGhost(dt, dt.TypeArgs);

      if (dt is CoDatatypeDecl) {
        wr.WriteLine($"public override {DtTypeName(dt)} _Get() {{ return this; }}");
      }

      CompileDatatypeDowncastClone(dt, wr, nonGhostTypeArgs, ctor: ctor);

      // Equals method
      {
        var w = wr.NewBlock("public override bool Equals(object other)");
        w.WriteLine($"var oth = other as {DtCtorName(ctor)}{TypeParameters(nonGhostTypeArgs)};");
        w.Write("return oth != null");
        i = 0;
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost) {
            var nm = FieldName(arg, i);
            w.Write(IsDirectlyComparable(DatatypeWrapperEraser.SimplifyType(arg.Type))
              ? $" && this.{nm} == oth.{nm}"
              : $" && object.Equals(this.{nm}, oth.{nm})");

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
            string nm = FieldName(arg, i);
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

                  if (arg.Type.IsStringType && UnicodeCharEnabled) {
                    w.WriteLine($"{tempVar} += this.{FieldName(arg, i)}.ToVerbatimString(true);");
                  } else {
                    w.WriteLine($"{tempVar} += {DafnyHelpersClass}.ToString(this.{FieldName(arg, i)});");
                  }

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

    private string FieldName(Formal formal, int i) {
      Contract.Requires(formal != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return IdProtect("_" + (formal.HasName ? formal.CompileName : "a" + i));
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
      var dtName = dt.EnclosingModuleDefinition.IsDefaultModule ? IdName(dt) : dt.FullCompileName;
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }

    string DtCreateName(DatatypeCtor ctor) {
      Contract.Assert(!ctor.IsGhost); // there should never be an occasion to ask for a ghost constructor
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      } else {
        return "create_" + ctor.CompileName;
      }
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(nt.EnclosingModuleDefinition.CompileName), IdName(nt), nt, wr);
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var wEnum = w.NewBlock($"public static System.Collections.Generic.IEnumerable<{GetNativeTypeName(nt.NativeType)}> IntegerRange(BigInteger lo, BigInteger hi)");
        wEnum.WriteLine($"for (var j = lo; j < hi; j++) {{ yield return ({GetNativeTypeName(nt.NativeType)})j; }}");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var wrWitness = new ConcreteSyntaxTree();
        var wStmts = w.Fork();
        TrExpr(nt.Witness, wrWitness, false, wStmts);
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
      var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var sw = new ConcreteSyntaxTree(cw.InstanceMemberWriter.RelativeIndentLevel);
        var wStmts = cw.InstanceMemberWriter.Fork();
        TrExpr(sst.Witness, sw, false, wStmts);
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

    protected class ClassWriter : IClassWriter {
      public readonly CsharpCompiler Compiler;
      public readonly ConcreteSyntaxTree InstanceMemberWriter;
      public readonly ConcreteSyntaxTree StaticMemberWriter;
      public readonly ConcreteSyntaxTree CtorBodyWriter;
      private readonly CsharpSynthesizer csharpSynthesizer;

      public ClassWriter(CsharpCompiler compiler, ConcreteSyntaxTree instanceMemberWriter, ConcreteSyntaxTree/*?*/ ctorBodyWriter, ConcreteSyntaxTree/*?*/ staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.CtorBodyWriter = ctorBodyWriter;
        this.StaticMemberWriter = staticMemberWriter ?? instanceMemberWriter;
        this.csharpSynthesizer = new CsharpSynthesizer(Compiler, ErrorWriter());
      }

      public ConcreteSyntaxTree Writer(bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        if (createBody) {
          if (isStatic || (member?.EnclosingClass is TraitDecl && Compiler.NeedsCustomReceiver(member))) {
            return StaticMemberWriter;
          }
        }

        return InstanceMemberWriter;
      }

      public ConcreteSyntaxTree /*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, Writer(m.IsStatic, createBody, m), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method method, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance,
        bool lookasideBody) {
        return csharpSynthesizer.SynthesizeMethod(method, typeArgs, createBody, Writer(method.IsStatic, createBody, method), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree /*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic, createBody, member), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree /*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl /*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic, createBody, member));
      }

      public ConcreteSyntaxTree /*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl /*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, createBody, out setterWriter, Writer(false, createBody, member));
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field field) {
        var typeName = Compiler.TypeName(type, this.StaticMemberWriter, tok);
        Compiler.DeclareField(name, true, isStatic, isConst, typeName, rhs, this);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException(); // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
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

      if (!createBody && m is Constructor) { return null; }

      wr.Format($"{keywords}{returnType} {IdName(m)}{typeParameters}({parameters})");

      if (!createBody || hasDllImportAttribute) {
        wr.WriteLine(";");
        return null;
      }

      var block = wr.NewBlock(open: BlockStyle.NewlineBrace);
      if (returnType != "void" && !forBodyInheritance) {
        var beforeReturnBlock = block.Fork();
        EmitReturn(m.Outs, block);
        return beforeReturnBlock;
      }

      return block;
    }

    internal string Keywords(bool isPublic = false, bool isStatic = false, bool isExtern = false) {
      return (isPublic ? "public " : "") + (isStatic ? "static " : "") + (isExtern ? "extern " : "") + (Synthesize && !isStatic && isPublic ? "virtual " : "");
    }

    internal ConcreteSyntaxTree GetMethodParameters(Method m, List<TypeArgumentInstantiation> typeArgs, bool lookasideBody, bool customReceiver, string returnType) {
      var parameters = GetFunctionParameters(m.Ins, m, typeArgs, lookasideBody, customReceiver);
      if (returnType == "void") {
        WriteFormals(parameters.Nodes.Any() ? ", " : "", m.Outs, parameters);
      }
      return parameters;
    }

    private ConcreteSyntaxTree GetFunctionParameters(List<Formal> formals, MemberDecl m, List<TypeArgumentInstantiation> typeArgs, bool lookasideBody, bool customReceiver) {
      var parameters = new ConcreteSyntaxTree();
      var sep = "";
      WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, m.EnclosingClass, m, lookasideBody), parameters, ref sep,
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

    internal string GetTargetReturnTypeReplacement(Method m, ConcreteSyntaxTree wr) {
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

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
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

      return wr.NewBlock(open: formals.Count > 1 ? BlockStyle.NewlineBrace : BlockStyle.SpaceBrace);
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody, ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree/*?*/ result = null;
      var body = createBody ? Block(out result, close: BlockStyle.Brace) : new ConcreteSyntaxTree().Write(";");
      wr.FormatLine($"{Keywords(createBody, isStatic)}{TypeName(resultType, wr, tok)} {name} {{ get{body} }}");
      return result;
    }

    protected ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree wr) {
      wr.Write($"{Keywords(createBody)}{TypeName(resultType, wr, tok)} {name}");
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
      Contract.Assume(member is Method { IsTailRecursive: true } or Function { IsTailRecursive: true }); // precondition
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        var receiverType = member.EnclosingClass is DatatypeDecl dt ? DtTypeName(dt) : "var";
        wr.WriteLine($"{receiverType} _this = this;");
      }
      wr.Fork(-1).WriteLine("TAIL_CALL_START: ;");
      return wr;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("goto TAIL_CALL_START;");
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(type);
      if (xType is BoolType) {
        return "bool";
      } else if (xType is CharType) {
        return CharTypeName;
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

    // To improve readability
    private static bool CharIsRune => UnicodeCharEnabled;
    private static string CharTypeName => UnicodeCharEnabled ? "Dafny.Rune" : "char";
    private static string CharTypeDescriptorName => DafnyHelpersClass + (UnicodeCharEnabled ? ".RUNE" : ".CHAR");

    private void ConvertFromChar(Expression e, ConcreteSyntaxTree wr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      if (e.Type.IsCharType && UnicodeCharEnabled) {
        wr.Write("(");
        TrParenExpr(e, wr, inLetExprBody, wStmts);
        wr.Write(".Value)");
      } else {
        TrParenExpr(e, wr, inLetExprBody, wStmts);
      }
    }

    public string TypeHelperName(Type type, ConcreteSyntaxTree wr, IToken tok, Type/*?*/ otherType = null) {
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

    public string CommonTypeName(Type a, Type /*?*/ b, ConcreteSyntaxTree wr, IToken tok) {
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

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();

      if (usePlaceboValue) {
        return $"default({TypeName(type, wr, tok)})";
      }

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return UnicodeCharEnabled ? $"new {CharTypeName}({CharType.DefaultValueAsString})" : CharType.DefaultValueAsString;
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
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            // non-null array type; we know how to initialize them
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out var typeNameSansBrackets, out var brackets);
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
          return $"(({TypeName(xType, wr, udt.tok)})null)";
        }
      } else if (cl is DatatypeDecl dt) {
        var s = FullTypeName(udt, ignoreInterface: true);
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

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments = false) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance.Count == typeArgs.Count);
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0) {
        s += "<" + TypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      if (type is UserDefinedType udt) {
        var name = udt.ResolvedClass is TraitDecl ? udt.FullCompanionCompileName : FullTypeName(udt, member, true);
        return TypeName_UDT(name, udt, wr, tok);
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

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      type = DatatypeWrapperEraser.SimplifyType(type, true);
      if (type is BoolType) {
        return "Dafny.Helpers.BOOL";
      } else if (type is CharType) {
        return CharTypeDescriptorName;
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

        return AddTypeDescriptorArgs(FullTypeName(udt, ignoreInterface: true), udt, relevantTypeArgs, wr, tok);
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

    private string AddTypeDescriptorArgs(string fullCompileName, UserDefinedType udt, List<Type> typeDescriptors, ConcreteSyntaxTree wr, IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(udt != null);
      Contract.Requires(typeDescriptors != null);
      Contract.Requires(wr != null);
      Contract.Requires(tok != null);

      var s = TypeName_UDT(fullCompileName, udt, wr, tok);
      s += $".{TypeDescriptorMethodName}({typeDescriptors.Comma(arg => TypeDescriptor(arg, wr, tok))})";
      return s;
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isPublic, bool isStatic, bool isConst, string typeName, string rhs, ClassWriter cw) {
      var publik = isPublic ? "public" : "private";
      var konst = isConst ? " readonly" : "";
      var virtuall = Synthesize ? " virtual" : "";
      if (isStatic) {
        cw.StaticMemberWriter.Write($"{publik} static{konst} {typeName} {name}");
        if (rhs != null) {
          cw.StaticMemberWriter.Write($" = {rhs}");
        }
        cw.StaticMemberWriter.WriteLine(";");
      } else {
        string ending = "";
        if (isPublic) {
          if (isConst) {
            cw.InstanceMemberWriter.Write(
              $"{publik}{konst}{virtuall} {typeName} {name} {{get;}}");
          } else {
            cw.InstanceMemberWriter.Write(
              $"{publik}{virtuall} {typeName} {name} {{get; set;}}");
          }
        } else {
          cw.InstanceMemberWriter.WriteLine($"{publik}{konst} {typeName} {name}");
          ending = ";";
        }
        if (cw.CtorBodyWriter == null) {
          if (rhs != null) {
            cw.InstanceMemberWriter.Write($" = {rhs}");
            ending = ";";
          }
        } else {
          if (rhs != null) {
            cw.CtorBodyWriter.WriteLine($"this.{name} = {rhs};");
          }
        }
        cw.InstanceMemberWriter.WriteLine(ending);
      }
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      wr.Write($"{prefix}{(isInParam ? "" : "out ")}{TypeName(type, wr, tok)} {name}");
      return true;
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, ConcreteSyntaxTree wr) {
      wr.Write($"{(type != null ? TypeName(type, wr, tok) : "var")} {name}");
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine($" = {rhs};");
      } else {
        wr.WriteLine(";");
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type/*?*/ type, IToken/*?*/ tok, ConcreteSyntaxTree wr) {
      var w = new ConcreteSyntaxTree();
      wr.FormatLine($"{(type != null ? TypeName(type, wr, tok) : "var")} {name} = {w};");
      return w;
    }

    protected override void DeclareOutCollector(string collectorVarName, ConcreteSyntaxTree wr) {
      wr.Write($"var {collectorVarName} = ");
    }

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
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

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (typeArgs.Count != 0) {
        wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
      }
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, ConcreteSyntaxTree wr, IToken tok) {
      return (type != null ? TypeName(type, wr, tok) : "var") + " " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      var typeArgs = arg.Type.AsArrowType == null ? "" : $"<{TypeName(arg.Type, wr, null, null)}>";
      var suffix = arg.Type.IsStringType && UnicodeCharEnabled ? ".ToVerbatimString(false)" : "";
      wr.WriteLine($"{DafnyHelpersClass}.Print{typeArgs}(({Expr(arg, false, wStmts)}){suffix});");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      var returnExpr = outParams.Count == 1 ? IdName(outParams[0]) : "";
      wr.WriteLine($"return {returnExpr};");
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var w = wr.Fork();
      var prefix = createContinueLabel ? "continue_" : "after_";
      wr.Fork(-1).WriteLine($"{prefix}{label}: ;");
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, ConcreteSyntaxTree wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("goto after_{0};", label);
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine("goto continue_{0};", label);
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

    protected override void EmitHalt(IToken tok, Expression/*?*/ messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("throw new Dafny.HaltException(");
      if (tok != null) {
        wr.Write(SymbolDisplay.FormatLiteral(ErrorReporter.TokenToString(tok) + ": ", true) + " + ");
      }

      TrExpr(messageExpr, wr, false, wStmts);
      if (UnicodeCharEnabled && messageExpr.Type.IsStringType) {
        wr.Write(".ToVerbatimString(false)");
      }

      wr.WriteLine(");");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {

      wr.Write($"for ({TypeName(loopIndex.Type, wr, tok)} {loopIndex.CompileName} = ");
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
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
      start = start ?? "0";
      return wr.NewNamedBlock("for (var {0} = {2}; {0} < {1}; {0}++)", indexVar, bound, start);
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

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      wr.Format($"foreach ({TypeName(collectionElementType, wr, tok)} {tmpVarName} in {collectionWriter})");
      return wr.NewBlock();
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      var typeName = TypeName(boundVarType, wr, tok);
      wr.WriteLine("{0}{1} = ({2}){3};", introduceBoundVar ? typeName + " " : "", boundVarName, typeName, tmpVarName);
    }

    [CanBeNull]
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      string typeTest;
      if (boundVarType.IsRefType) {
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          typeTest = "true";
        } else {
          typeTest = $"{tmpVarName} is {TypeName(boundVarType, wPreconditions, tok)}";
        }
        if (boundVarType.IsNonNullRefType) {
          typeTest = $"{tmpVarName} != null && {typeTest}";
        } else {
          typeTest = $"{tmpVarName} == null || {typeTest}";
        }
      } else {
        typeTest = "true";
      }

      return typeTest == "true" ? null : typeTest;
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      return wr.Format($"foreach (var {boundVarName} in {collectionWriter})").NewBlock();
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall /*?*/, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var cl = ((UserDefinedType)type.NormalizeExpand()).ResolvedClass;
      var ctor = (Constructor)initCall?.Method;  // correctness of cast follows from precondition of "EmitNew"
      var arguments = new ConcreteSyntaxTree();
      wr.Format($"new {TypeName(type, wr, tok)}({arguments})");
      var sep = "";
      EmitTypeDescriptorsActuals(TypeArgumentInstantiation.ListFromClass(cl, type.TypeArgs), tok, arguments, ref sep);
      arguments.Write(ConstructorArguments(initCall, wStmts, ctor, sep));
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var wrs = EmitNewArray(elementType, tok, dimensions.Count, mustInitialize, wr);
      for (var i = 0; i < wrs.Count; i++) {
        wrs[i].Write(dimensions[i]);
      }
    }

    private List<ConcreteSyntaxTree> EmitNewArray(Type elmtType, IToken tok, int dimCount, bool mustInitialize, ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree EmitSizeCheckWrapper(ConcreteSyntaxTree w) {
        w.Write($"{DafnyHelpersClass}.ToIntChecked(");
        var wSize = w.Fork();
        w.Write(", \"array size exceeds memory limit\")");
        return wSize;
      }

      var wrs = new List<ConcreteSyntaxTree>();
      if (!mustInitialize || HasSimpleZeroInitializer(elmtType)) {
        TypeName_SplitArrayName(elmtType, wr, tok, out string typeNameSansBrackets, out string brackets);
        wr.Write("new {0}", typeNameSansBrackets);
        string prefix = "[";
        for (var d = 0; d < dimCount; d++) {
          wr.Write(prefix);
          wrs.Add(EmitSizeCheckWrapper(wr));
          prefix = ", ";
        }
        wr.Write("]{0}", brackets);
      } else {
        wr.Write("Dafny.ArrayHelpers.InitNewArray{0}<{1}>", dimCount, TypeName(elmtType, wr, tok));
        var inParens = wr.ForkInParens();
        inParens.Write(DefaultValue(elmtType, inParens, tok, true));
        for (var d = 0; d < dimCount; d++) {
          inParens.Write(", ");
          wrs.Add(EmitSizeCheckWrapper(inParens));
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
        var v = (string)e.Value;
        if (UnicodeCharEnabled) {
          var codePoint = Util.UnescapedCharacters(v, false).Single();
          if (codePoint > char.MaxValue) {
            // C# supports \U, but doesn't allow values that require two UTF-16 code units in character literals.
            // For such values we construct the Rune value directly from the unescaped codepoint.
            wr.Write($"new Dafny.Rune(0x{codePoint:x})");
          } else {
            wr.Write($"new Dafny.Rune('{Util.ExpandUnicodeEscapes(v, false)}')");
          }
        } else {
          wr.Write($"'{v}'");
        }
      } else if (e is StringLiteralExpr str) {
        wr.Format($"{DafnySeqClass}<{CharTypeName}>.{CharMethodQualifier}FromString({StringLiteral(str)})");
      } else if (AsNativeType(e.Type) != null) {
        GetNativeInfo(AsNativeType(e.Type).Sel, out var nativeName, out var literalSuffix, out var needsCastAfterArithmetic);
        if (needsCastAfterArithmetic) {
          wr = wr.Write($"({nativeName})").ForkInParens();
        }
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
      wr.Write($"{(isVerbatim ? "@" : "")}\"{Util.ExpandUnicodeEscapes(str, false)}\"");
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string nativeName = null, literalSuffix = null;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out var needsCastAfterArithmetic);
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

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
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
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, nativeType, true, wr.ForkInParens(), inLetExprBody, wStmts, tr);

      wr.Write(" | ");

      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, nativeType, false, wr.ForkInParens(), inLetExprBody, wStmts, tr);
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType nativeType /*?*/, bool firstOp,
        ConcreteSyntaxTree wr, bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody, wStmts);
      wr.Write(" {0} ", op);
      if (!firstOp) {
        wr = wr.ForkInParens().Write("{0} - ", bv.Width);
      }

      wr.Write("(int)");
      tr(e1, wr.ForkInParens(), inLetExprBody, wStmts);
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
      wr.Write($"{prefix}.Item{i + 1}");
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public override string PublicIdProtect(string name) {
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

    protected override string FullTypeName(UserDefinedType udt, MemberDecl /*?*/ member = null) {
      return FullTypeName(udt, member);
    }
    private string FullTypeName(UserDefinedType udt, MemberDecl/*?*/ member = null, bool ignoreInterface = false) {
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

      //Use the interface if applicable (not handwritten, or incompatible variance)
      if ((cl is DatatypeDecl)
          && !ignoreInterface
          && (member is null || !NeedsCustomReceiver(member))) {
        return (cl.EnclosingModuleDefinition.IsDefaultModule ? "" : IdProtect(cl.EnclosingModuleDefinition.CompileName) + ".") + DtTypeName(cl, false);
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
        (enclosingMethod != null && (enclosingMethod.IsTailRecursive || NeedsCustomReceiver(enclosingMethod))) ||
        (enclosingFunction != null && (enclosingFunction.IsTailRecursive || NeedsCustomReceiver(enclosingFunction))) ||
        thisContext is NewtypeDecl ||
        thisContext is TraitDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.FullCompileName;

      var nonGhostInferredTypeArgs = SelectNonGhost(dt, dtv.InferredTypeArgs);
      var typeParams = nonGhostInferredTypeArgs.Count == 0 ? "" : $"<{TypeNames(nonGhostInferredTypeArgs, wr, dtv.tok)}>";
      if (!dtv.IsCoCall) {
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   Dt.create_Cons<T>( args )
        wr.Write($"{dtName}{typeParams}.{DtCreateName(dtv.Ctor)}({arguments})");
      } else {
        // In the case of a co-recursive call, generate:
        //     new Dt__Lazy<T>( LAMBDA )
        // where LAMBDA is:
        //     () => { return Dt_Cons<T>( ...args... ); }
        wr.Write($"new {dtName}__Lazy{typeParams}(");
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
          compiledName = idParam == null ? "Length" : $"GetLength({(int)idParam})";
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
          var domainType = TypeName(mapType.Domain, errorWr, Token.NoToken);
          var rangeType = TypeName(mapType.Range, errorWr, Token.NoToken);
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
      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(member);
      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        return SimpleLvalue(obj);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return SimpleLvalue(w => w.Write("true"));
      } else if (member is SpecialField sf && !(member is ConstantField)) {
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
          EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), fn.tok, callArguments, ref sep);
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
              var ty = arg.Type.Subst(typeMap);
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
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w, ref sep);
            if (sep != "(") {
              w.Write(")");
            }
          });
        } else if (NeedsCustomReceiver(member) && !(member.EnclosingClass is TraitDecl)) {
          // instance const in a newtype or belongs to a datatype
          Contract.Assert(typeArgs.Count == 0 || member.EnclosingClass is DatatypeDecl);
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

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      wr.Write("[");
      var sep = "";
      foreach (var index in indices) {
        wr.Write("{0}(int)", sep);
        TrParenExpr(index, wr, inLetExprBody, wStmts);
        sep = ", ";
      }
      wr.Write("]");
      return w;
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr("(int)", expr, wr, inLetExprBody, wStmts);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var xType = source.Type.NormalizeExpand();
      if (xType is MapType) {
        var inner = wr.Write(TypeHelperName(xType, wr, source.tok) + ".Select").ForkInParens();
        TrExpr(source, inner, inLetExprBody, wStmts);
        inner.Write(",");
        TrExpr(index, inner, inLetExprBody, wStmts);
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        TrParenExpr(".Select", index, wr, inLetExprBody, wStmts);
      }
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var xType = source.Type.NormalizeExpand();
      if (xType is SeqType || xType is MapType) {
        wr.Write(TypeHelperName(xType, wr, source.tok) + ".Update");
        wr.Append(ParensList(
          Expr(source, inLetExprBody, wStmts),
          Expr(index, inLetExprBody, wStmts),
          Expr(value, inLetExprBody, wStmts)));
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".Update");
        wr.Append(ParensList(
          Expr(index, inLetExprBody, wStmts),
          Expr(value, inLetExprBody, wStmts)));
      }
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo /*?*/, Expression hi /*?*/,
      bool fromArray, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (fromArray) {
        wr.Write($"{DafnyHelpersClass}.SeqFromArray");
      }
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      if (hi != null) {
        if (lo != null) {
          wr.Write(".Subsequence");
          wr.Append(ParensList(Expr(lo, inLetExprBody, wStmts), Expr(hi, inLetExprBody, wStmts)));
        } else {
          TrParenExpr(".Take", hi, wr, inLetExprBody, wStmts);
        }
      } else {
        if (lo != null) {
          TrParenExpr(".Drop", lo, wr, inLetExprBody, wStmts);
        }
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      if (expr.Initializer is LambdaExpr lam) {
        Contract.Assert(lam.BoundVars.Count == 1);
        EmitSeqConstructionExprFromLambda(expr.N, lam.BoundVars[0], lam.Body, inLetExprBody, wr);
      } else {
        wr.Write($"{DafnySeqClass}<{TypeName(expr.Type.AsSeqType.Arg, wr, expr.tok)}>.Create");
        wr.Append(ParensList(Expr(expr.N, inLetExprBody, wStmts), Expr(expr.Initializer, inLetExprBody, wStmts)));
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
      var lengthVar = idGenerator.FreshId("dim");
      DeclareLocalVar(lengthVar, indexType, lengthExpr.tok, lengthExpr, inLetExprBody, wrLamBody);
      var arrVar = idGenerator.FreshId("arr");
      wrLamBody.Write($"var {arrVar} = ");
      var wrDims = EmitNewArray(body.Type, body.tok, dimCount: 1, mustInitialize: false, wr: wrLamBody);
      Contract.Assert(wrDims.Count == 1);
      wrDims[0].Write(lengthVar);
      wrLamBody.WriteLine(";");

      var intIxVar = idGenerator.FreshId("i");
      var wrLoopBody = wrLamBody.NewBlock(string.Format("for (int {0} = 0; {0} < {1}; {0}++)", intIxVar, lengthVar));
      var ixVar = IdName(boundVar);
      wrLoopBody.WriteLine("var {0} = ({1}) {2};",
        ixVar, TypeName(indexType, wrLoopBody, body.tok), intIxVar);
      var wrArrName = EmitArrayUpdate(new List<string> { ixVar }, body, wrLoopBody);
      wrArrName.Write(arrVar);
      EndStmt(wrLoopBody);

      wrLamBody.WriteLine("return {0}<{1}>.FromArray({2});", DafnySeqClass, TypeName(body.Type, wr, body.tok), arrVar);
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      wr.Write("{0}<{1}>", DafnyMultiSetClass, TypeName(expr.E.Type.AsCollectionType.Arg, wr, expr.tok));
      var eeType = expr.E.Type.NormalizeExpand();
      if (eeType is SeqType) {
        TrParenExpr(".FromSeq", expr.E, wr, inLetExprBody, wStmts);
      } else if (eeType is SetType) {
        TrParenExpr(".FromSet", expr.E, wr, inLetExprBody, wStmts);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyHelpersClass}.Id<{TypeName(functionType, wr, tok)}>({Expr(function, inLetExprBody, wStmts)})");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IToken tok, ConcreteSyntaxTree wr) {
      from = from.NormalizeExpand();
      to = to.NormalizeExpand();
      Contract.Assert(from.IsRefType == to.IsRefType);

      var w = new ConcreteSyntaxTree();
      if (to.IsRefType) {
        wr.Format($"(({TypeName(to, wr, tok)})({w}))");
      } else {
        Contract.Assert(Type.SameHead(from, to));

        var typeArgs = from.IsArrowType ? from.TypeArgs.Concat(to.TypeArgs) : to.TypeArgs;
        var wTypeArgs = typeArgs.Comma(ta => TypeName(ta, wr, tok));
        var argPairs = from.TypeArgs.Zip(to.TypeArgs);
        if (from.IsArrowType) {
          argPairs = argPairs.Select((tp, i) => ++i < to.TypeArgs.Count ? (tp.Second, tp.First) : tp);
        }
        var wConverters = argPairs.Comma(t => DowncastConverter(t.Item1, t.Item2, wr, tok));
        DatatypeDecl dt = from.AsDatatype;
        if (dt != null && DowncastCloneNeedsCustomReceiver(dt)) {
          wr.Format($"{TypeName_Companion(from, wr, tok, null)}.DowncastClone<{wTypeArgs}>({w}, {wConverters})");
        } else {
          wr.Format($"({w}).DowncastClone<{wTypeArgs}>({wConverters})");
        }
        Contract.Assert(from.TypeArgs.Count == to.TypeArgs.Count);
      }
      return w;
    }

    bool DowncastCloneNeedsCustomReceiver(DatatypeDecl dt) {
      return SelectNonGhost(dt, dt.TypeArgs).Any(ty => ty.Variance == TypeParameter.TPVariance.Contra) ||
             DatatypeWrapperEraser.IsErasableDatatypeWrapper(dt, out _);
    }

    string DowncastConverter(Type from, Type to, ConcreteSyntaxTree errorWr, IToken tok) {
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

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken tok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      var tas = Util.Snoc(boundTypes, resultType);
      var typeArgs = TypeName_UDT(ArrowType.Arrow_FullCompileName, tas.ConvertAll(_ => TypeParameter.TPVariance.Non), tas, wr, tok);
      var result = new ConcreteSyntaxTree();
      wr.Format($"{DafnyHelpersClass}.Id<{typeArgs}>(({boundVars.Comma()}) => {result})");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return result;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
        wr.Write(source);
      } else {
        wr.Write($"{source}.{DestructorGetterName(dtor, ctor, formalNonGhostIndex)}");
      }
    }

    private string DestructorGetterName(Formal dtor, DatatypeCtor ctor, int index) {
      return $"dtor_{(dtor.HasName ? dtor.CompileName : ctor.CompileName + FieldName(dtor, index))}";
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
      Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
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
        wr.Write($"(System.Func<{inTypes.Concat(new[] { resultType }).Comma(t => TypeName(t, wr, tok))}>)");
      }
      wr.Format($"(({inNames.Comma(nm => nm)}) =>{ExprBlock(out ConcreteSyntaxTree body)})");
      return body;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wrRhs = new ConcreteSyntaxTree();
      wrBody = new ConcreteSyntaxTree();
      wr.Format($"{DafnyHelpersClass}.Let<{TypeName(bvType, wr, bvTok)}, {TypeName(bodyType, wr, bodyTok)}>({wrRhs}, {bvName} => {wrBody})");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      // (
      //   (System.Func<resultType>)(() => <<body>>)
      // )()
      wr.Format($"((System.Func<{TypeName(resultType, wr, resultTok)}>)(() =>{ExprBlock(out ConcreteSyntaxTree result)}))()");
      return result;
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Format($"{DafnyHelpersClass}.Let<int, {TypeName(resultType, wr, resultTok)}>({source}, {bvName} => {Block(out ConcreteSyntaxTree result)})");
      return result;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr("new BigInteger(", expr, wr, inLetExprBody, wStmts);
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
        case BinaryExpr.ResolvedOpcode.EqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (eqType.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "== (object)";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "==";
            } else {
              staticCallString = "object.Equals";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
            } else if (eqType.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "!= (object)";
            } else if (IsDirectlyComparable(eqType)) {
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
          if (resultType.IsCharType) {
            if (CharIsRune) {
              staticCallString = $"{DafnyHelpersClass}.AddRunes";
            } else {
              opString = "+"; truncateResult = true;
              preOpString = $"(char)(";
              postOpString = ")";
            }
          } else {
            opString = "+"; truncateResult = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          if (resultType.IsCharType) {
            if (CharIsRune) {
              staticCallString = $"{DafnyHelpersClass}.SubtractRunes";
            } else {
              opString = "-"; truncateResult = true;
              preOpString = $"(char)(";
              postOpString = ")";
            }
          } else {
            opString = "-"; truncateResult = true;
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*"; truncateResult = true; break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (NeedsEuclideanDivision(resultType)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyHelpersClass}.EuclideanDivision{suffix}";
          } else {
            opString = "/";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (NeedsEuclideanDivision(resultType)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyHelpersClass}.EuclideanModulus{suffix}";
          } else {
            opString = "%";
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
        case BinaryExpr.ResolvedOpcode.InSeq:
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

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("new Dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("new BigInteger");
          }
          ConvertFromChar(e.E, wr, inLetExprBody, wStmts);
          wr.Write(", BigInteger.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write($"({CharTypeName})");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative == null && toNative == null) {
            if (e.E.Type.IsCharType) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("new BigInteger");
              ConvertFromChar(e.E, wr, inLetExprBody, wStmts);
            } else {
              // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
              TrExpr(e.E, wr, inLetExprBody, wStmts);
            }
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("new BigInteger");
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
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
              TrParenExpr(u.E, wr, inLetExprBody, wStmts);
              if (toNative.UpperBound <= new BigInteger(0x80000000U)) {
                wr.Write(".Count");
              } else {
                wr.Write(".LongCount");
              }
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              TrParenExpr(m.Obj, wr, inLetExprBody, wStmts);
              if (toNative.UpperBound <= new BigInteger(0x80000000U)) {
                wr.Write(".Length");
              } else {
                wr.Write(".LongLength");
              }
            } else {
              // no optimization applies; use the standard translation
              ConvertFromChar(e.E, wr, inLetExprBody, wStmts);
            }
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody, wStmts);
        } else {
          // real -> (int or bv or char or ordinal)
          if (e.ToType.IsCharType) {
            wr.Write($"({CharTypeName})");
          } else if (AsNativeType(e.ToType) != null) {
            wr.Write("({0})", GetNativeTypeName(AsNativeType(e.ToType)));
          }
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
          wr.Write(".ToBigInteger()");
        }
      } else if (e.E.Type.IsBigOrdinalType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int) || e.ToType.IsBigOrdinalType) {
          TrExpr(e.E, wr, inLetExprBody, wStmts);
        } else if (e.ToType.IsCharType) {
          wr.Write($"({CharTypeName})");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
        } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          wr.Write("new Dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("new BigInteger");
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
            wr.Write(", BigInteger.One)");
          } else {
            TrParenExpr(e.E, wr, inLetExprBody, wStmts);
            wr.Write(", 1)");
          }
        } else if (e.ToType.IsBitVectorType) {
          // ordinal -> bv
          var typename = TypeName(e.ToType, wr, null, null);
          wr.Write($"({typename})");
          TrParenExpr(e.E, wr, inLetExprBody, wStmts);
        } else {
          Contract.Assert(false, $"not implemented for C#: {e.E.Type} -> {e.ToType}");
        }
      } else {
        Contract.Assert(false, $"not implemented for C#: {e.E.Type} -> {e.ToType}");
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
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
        throw new UnsupportedFeatureException(tok, Feature.SubsetTypeTests);
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("{0}.FromElements", TypeHelperName(ct, wr, tok));
      TrExprList(elements, wr, inLetExprBody, wStmts);
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var arguments = elements.Select(p => {
        var result = new ConcreteSyntaxTree();
        result.Format($"new Dafny.Pair{BracketList((LineSegment)TypeName(p.A.Type, result, p.A.tok), (LineSegment)TypeName(p.B.Type, result, p.B.tok))}");
        result.Append(ParensList(Expr(p.A, inLetExprBody, wStmts), Expr(p.B, inLetExprBody, wStmts)));
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
        var wStmts = wr.Fork();
        wr.FormatLine($"{collName}.Add({Expr(elmt, inLetExprBody, wStmts)});");
      } else {
        Contract.Assume(false);  // unexpected collection type
      }
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var domtypeName = TypeName(mt.Domain, wr, tok);
      var rantypeName = TypeName(mt.Range, wr, tok);
      var termLeftWriter = new ConcreteSyntaxTree();
      var wStmts = wr.Fork();
      wr.FormatLine($"{collName}.Add(new Dafny.Pair<{domtypeName},{rantypeName}>{ParensList(termLeftWriter, Expr(term, inLetExprBody, wStmts))});");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
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

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyHelpersClass}.SingleValue<{type}>");
      TrParenExpr(e, wr, inLetExprBody, wStmts);
    }

    private void AddTestCheckerIfNeeded(string name, Declaration decl, ConcreteSyntaxTree wr) {
      if (DafnyOptions.O.Compile || DafnyOptions.O.RunAllTests || !Attributes.Contains(decl.Attributes, "test")) {
        return;
      }

      var firstReturnIsFailureCompatible = false;
      var returnTypesCount = 0;

      if (decl is Function func) {
        returnTypesCount = 1;
        firstReturnIsFailureCompatible =
          func.ResultType?.AsTopLevelTypeWithMembers?.Members?.Any(m => m.Name == "IsFailure") ?? false;
      } else if (decl is Method method) {
        returnTypesCount = method.Outs.Count;
        if (returnTypesCount > 0) {
          firstReturnIsFailureCompatible =
            method.Outs[0].Type?.AsTopLevelTypeWithMembers?.Members?.Any(m => m.Name == "IsFailure") ?? false;
        }
      }

      wr.WriteLine("[Xunit.Fact]");
      if (!firstReturnIsFailureCompatible) {
        return;
      }

      wr = wr.NewNamedBlock("public static void {0}_CheckForFailureForXunit()", name);
      var returnsString = string.Join(",", Enumerable.Range(0, returnTypesCount).Select(i => $"r{i}"));
      wr.FormatLine($"var {returnsString} = {name}();");
      wr.WriteLine("Xunit.Assert.False(r0.IsFailure(), \"Dafny test failed: \" + r0);");

    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), wr, mainMethod.tok, mainMethod);
      var wClass = wr.NewNamedBlock("class __CallToMain");
      var wBody = wClass.NewNamedBlock("public static void Main(string[] args)");
      var modName = mainMethod.EnclosingClass.EnclosingModuleDefinition.CompileName == "_module" ? "_module." : "";
      companion = modName + companion;

      var idName = IssueCreateStaticMain(mainMethod) ? "_StaticMain" : IdName(mainMethod);

      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{GetHelperModuleName()}.WithHaltHandling(() => {companion}.{idName}(Dafny.Sequence<Dafny.ISequence<{CharTypeName}>>.{CharMethodQualifier}FromMainArguments(args)));");
      Coverage.EmitTearDown(wBody);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var tryBlock = wr.NewBlock("try");
      TrStmt(body, tryBlock);
      var catchBlock = wr.NewBlock("catch (Dafny.HaltException e)");
      catchBlock.WriteLine($"var {haltMessageVarName} = Dafny.Sequence<{CharTypeName}>.{CharMethodQualifier}FromString(e.Message);");
      TrStmt(recoveryBody, catchBlock);
    }

  }
}
