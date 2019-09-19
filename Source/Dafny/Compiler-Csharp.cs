//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.CodeDom.Compiler;
using System.Reflection;
using System.Collections.ObjectModel;
using Bpl = Microsoft.Boogie;



namespace Microsoft.Dafny
{
  public class CsharpCompiler : Compiler
  {
    public CsharpCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "C#";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine("// To recompile, use 'csc' with: /r:System.Numerics.dll");
      wr.WriteLine("// and choosing /target:exe or /target:library");
      wr.WriteLine("// You might also want to include compiler switches like:");
      wr.WriteLine("//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168");
      wr.WriteLine();
      wr.WriteLine("using System;");
      wr.WriteLine("using System.Numerics;");
      EmitDafnySourceAttribute(program, wr);
      ReadRuntimeSystem("DafnyRuntime.cs", wr);
    }

    void EmitDafnySourceAttribute(Program program, TextWriter wr) {
      Contract.Requires(program != null);
      Contract.Requires(wr != null);

      wr.WriteLine("[assembly: DafnyAssembly.DafnySourceAttribute(@\"");

      var strwr = new StringWriter();
      strwr.NewLine = wr.NewLine;
      new Printer(strwr, DafnyOptions.PrintModes.Everything).PrintProgram(program, true);

      wr.Write(strwr.GetStringBuilder().Replace("\"", "\"\"").ToString());
      wr.WriteLine("\")]");
      wr.WriteLine();
    }

    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
      wr = CreateModule("Dafny", false, false, null, wr);
      wr = wr.NewNamedBlock("internal class ArrayHelpers");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl) {
          int dims = ((ArrayClassDecl)decl).Dims;

          // Here is an overloading of the method name, where there is an initialValue parameter
          // public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
          wr.Write("public static T[");
          wr.RepeatWrite(dims, "", ",");
          wr.Write("] InitNewArray{0}<T>(T z, ", dims);
          wr.RepeatWrite(dims, "BigInteger size{0}", ", ");
          wr.Write(")");

          var w = wr.NewBlock("");
          // int s0 = (int)size0;
          for (int i = 0; i < dims; i++) {
            w.WriteLine("int s{0} = (int)size{0};", i);
          }
          // T[,] a = new T[s0, s1];
          w.Write("T[");
          w.RepeatWrite(dims, "", ",");
          w.Write("] a = new T[");
          w.RepeatWrite(dims, "s{0}", ",");
          w.WriteLine("];");
          // for (int i0 = 0; i0 < s0; i0++) {
          //   for (int i1 = 0; i1 < s1; i1++) {
          var wLoopNest = w;
          for (int i = 0; i < dims; i++) {
            wLoopNest = wLoopNest.NewNamedBlock("for (int i{0} = 0; i{0} < s{0}; i{0}++)", i);
          }
          // a[i0,i1] = z;
          wLoopNest.Write("a[");
          wLoopNest.RepeatWrite(dims, "i{0}", ",");
          wLoopNest.WriteLine("] = z;");
          // return a;
          w.WriteLine("return a;");
        }
      }
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = (cw as CsharpCompiler.ClassWriter).StaticMemberWriter;
      return wr.NewBlock("public static void Main(string[] args)");
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string/*?*/ libraryName, TargetWriter wr) {
      var s = string.Format("namespace {0}", IdProtect(moduleName));
      return wr.NewBigBlock(s, " // end of " + s);
    }

    protected override string GetHelperModuleName() => "Dafny.Helpers";

    string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => IdName(tp));
    }

    protected override IClassWriter CreateClass(string name, bool isExtern, string/*?*/ fullPrintName, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      wr.Write("public partial class {0}", name);
      if (typeParameters != null && typeParameters.Count != 0) {
        wr.Write("<{0}>", TypeParameters(typeParameters));
      }
      if (superClasses != null) {
        string sep = " : ";
        foreach (var trait in superClasses) {
          wr.Write("{0}{1}", sep, TypeName(trait, wr, tok));
          sep = ", ";
        }
      }
      return new ClassWriter(this, wr.NewBlock(""));
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type>/*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      wr.Write("public interface {0}", IdProtect(name));
      if (superClasses != null) {
        string sep = " : ";
        foreach (var trait in superClasses) {
          wr.Write("{0}{1}", sep, TypeName(trait, wr, tok));
          sep = ", ";
        }
      }
      var instanceMemberWriter = wr.NewBlock("");

      //writing the _Companion class
      wr.Write("public class _Companion_{0}", name);
      var staticMemberWriter = wr.NewBlock("");

      return new ClassWriter(this, instanceMemberWriter, staticMemberWriter);
    }

    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr) {
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

      var cw =
        CreateClass(IdName(iter), iter.TypeArgs, wr) as CsharpCompiler.ClassWriter;
      var w = cw.InstanceMemberWriter;
      // here come the fields
      Constructor ct = null;
      foreach (var member in iter.Members) {
        var f = member as Field;
        if (f != null && !f.IsGhost) {
          cw.DeclareField(IdName(f), false, false, f.Type, f.tok, DefaultValue(f.Type, w, f.tok));
        } else if (member is Constructor) {
          Contract.Assert(ct == null);  // we're expecting just one constructor
          ct = (Constructor)member;
        }
      }
      Contract.Assert(ct != null);  // we do expect a constructor
      w.WriteLine("System.Collections.Generic.IEnumerator<object> _iter;");

      // here's the initializer method
      w.Write("public void {0}(", IdName(ct));
      string sep = "";
      foreach (var p in ct.Ins) {
        if (!p.IsGhost) {
          // here we rely on the parameters and the corresponding fields having the same names
          w.Write("{0}{1} {2}", sep, TypeName(p.Type, w, p.tok), IdName(p));
          sep = ", ";
        }
      }
      using (var wBody = w.NewBlock(")")) {
        foreach (var p in ct.Ins) {
          if (!p.IsGhost) {
            wBody.WriteLine("this.{0} = {0};", IdName(p));
          }
        }
        wBody.WriteLine("this._iter = TheIterator();");
      }
      // here are the enumerator methods
      w.WriteLine("public bool MoveNext() { return _iter.MoveNext(); }");
      var wIter = w.NewBlock("private System.Collections.Generic.IEnumerator<object> TheIterator()");
      var suffix = new TargetWriter(wIter.IndentLevel);
      suffix.WriteLine("yield break;");
      wIter.BodySuffix = suffix.ToString();
      return wIter;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      var w = CompileDatatypeBase(dt, wr);
      CompileDatatypeConstructors(dt, wr);
      return w;
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, TargetWriter wr) {
      Contract.Requires(dt != null);
      Contract.Requires(wr != null);

      // public abstract class Dt<T> {  // for record types: drop "abstract"
      //   public Dt() { }
      //   static Dt<T> theDefault;
      //   public static Dt<T> Default {
      //     get {
      //       if (theDefault == null) {
      //         theDefault = ...;
      //       }
      //       return theDefault;
      //     }
      //   }
      //   public static Dt<T> _DafnyDefaultValue() { return Default; }
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
      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);
      string DtT_TypeArgs = "";
      if (dt.TypeArgs.Count != 0) {
        DtT_TypeArgs = "<" + TypeParameters(dt.TypeArgs) + ">";
        DtT += DtT_TypeArgs;
        DtT_protected += DtT_TypeArgs;
      }

      // from here on, write everything into the new block created here:
      var btw = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      wr = btw;

      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine("public {0}() {{ }}", IdName(dt));
      }

      wr.WriteLine("static {0} theDefault;", DtT_protected);

      using (var w = wr.NewNamedBlock("public static {0} Default", DtT_protected)) {
        var wGet = w.NewBlock("get");
        var wIf = EmitIf("theDefault == null", false, wGet);
        wIf.Write("theDefault = ");

        DatatypeCtor defaultCtor;
        if (dt is IndDatatypeDecl) {
          defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
        } else {
          defaultCtor = ((CoDatatypeDecl)dt).Ctors[0];  // pick any one of them (but pick must be the same as in InitializerIsKnown and HasZeroInitializer)
        }
        if (dt is CoDatatypeDecl) {
          wIf.Write("new {0}__Lazy{1}(", dt.CompileName, DtT_TypeArgs);
          wIf.Write("() => { return ");
        }
        wIf.Write("new {0}(", DtCtorName(defaultCtor, dt.TypeArgs));
        string sep = "";
        foreach (Formal f in defaultCtor.Formals) {
          if (!f.IsGhost) {
            wIf.Write("{0}{1}", sep, DefaultValue(f.Type, wIf, f.tok));
            sep = ", ";
          }
        }
        wIf.Write(");");
        if (dt is CoDatatypeDecl) {
          wIf.Write(" });");
        }
        wIf.WriteLine();

        wGet.WriteLine("return theDefault;");
      }

      wr.WriteLine("public static {0} _DafnyDefaultValue() {{ return Default; }}", DtT_protected);

      if (dt is CoDatatypeDecl) {
        wr.WriteLine("public abstract {0} _Get();", DtT_protected);
      }

      // create methods
      foreach (var ctor in dt.Ctors) {
        wr.Write("public static {0} {1}(", DtT_protected, DtCreateName(ctor));
        WriteFormals("", ctor.Formals, wr);
        var w = wr.NewBlock(")");
        w.Write("return new {0}(", DtCtorDeclarationName(ctor, dt.TypeArgs));
        var sep = "";
        var i = 0;
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.Write("{0}{1}", sep, FormalName(arg, i));
            sep = ", ";
            i++;
          }
        }
        w.WriteLine(");");
      }
      // query properties
      foreach (var ctor in dt.Ctors) {
        if (dt.IsRecordType) {
          // public bool is_Ctor0 { get { return true; } }
          wr.WriteLine("public bool is_{0} {{ get {{ return true; }} }}", ctor.CompileName);
        } else {
          // public bool is_Ctor0 { get { return this is Dt_Ctor0; } }
          wr.WriteLine("public bool is_{0} {{ get {{ return this is {1}_{0}{2}; }} }}", ctor.CompileName, dt.CompileName, DtT_TypeArgs);
        }
      }
      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        var w = wr.NewNamedBlock("public static System.Collections.Generic.IEnumerable<{0}> AllSingletonConstructors", DtT_protected);
        var wGet = w.NewBlock("get");
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          wGet.WriteLine("yield return {0}.{1}();", DtT_protected, DtCreateName(ctor));
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
              using (var wDtor = wr.NewNamedBlock("public {0} dtor_{1}", TypeName(arg.Type, wr, arg.tok), arg.CompileName)) {
                var wGet = wDtor.NewBlock("get");
                if (dt.IsRecordType) {
                  if (dt is CoDatatypeDecl) {
                    wGet.WriteLine("return this._Get().{0};", IdName(arg));
                  } else {
                    wGet.WriteLine("return this.{0};", IdName(arg));
                  }
                } else {
                  if (dt is CoDatatypeDecl) {
                    wGet.WriteLine("var d = this._Get();");
                  } else {
                    wGet.WriteLine("var d = this;");
                  }
                  var n = dtor.EnclosingCtors.Count;
                  for (int i = 0; i < n-1; i++) {
                    var ctor_i = dtor.EnclosingCtors[i];
                    Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                    wGet.WriteLine("if (d is {0}_{1}{2}) {{ return (({0}_{1}{2})d).{3}; }}", dt.CompileName, ctor_i.CompileName, DtT_TypeArgs, IdName(arg));
                  }
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n-1].CompileName);
                  wGet.WriteLine("return (({0}_{1}{2})d).{3}; ", dt.CompileName, dtor.EnclosingCtors[n-1].CompileName, DtT_TypeArgs, IdName(arg));
                }
              }
            }
          }
        }
      }

      return new ClassWriter(this, btw);
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

    void CompileDatatypeConstructors(DatatypeDecl dt, TargetWriter wrx) {
      Contract.Requires(dt != null);
      string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
      if (dt is CoDatatypeDecl) {
        // public class Dt__Lazy<T> : Dt<T> {
        //   public delegate Dt<T> Computer();
        //   Computer c;
        //   Dt<T> d;
        //   public Dt__Lazy(Computer c) { this.c = c; }
        //   public override Dt<T> _Get() { if (c != null) { d = c(); c = null; } return d; }
        //   public override string ToString() { return _Get().ToString(); }
        // }
        var w = wrx.NewNamedBlock("public class {0}__Lazy{2} : {1}{2}", dt.CompileName, IdName(dt), typeParams);
        w.WriteLine("public {2}delegate {0}{1} Computer();", dt.CompileName, typeParams, NeedsNew(dt, "Computer"));
        w.WriteLine("{0}Computer c;", NeedsNew(dt, "c"));
        w.WriteLine("{2}{0}{1} d;", dt.CompileName, typeParams, NeedsNew(dt, "d"));
        w.WriteLine("public {0}__Lazy(Computer c) {{ this.c = c; }}", dt.CompileName);
        w.WriteLine("public override {0}{1} _Get() {{ if (c != null) {{ d = c(); c = null; }} return d; }}", dt.CompileName, typeParams);
        w.WriteLine("public override string ToString() { return _Get().ToString(); }");
      }

      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }
      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var wr = wrx.NewNamedBlock("public class {0} : {1}{2}", DtCtorDeclarationName(ctor, dt.TypeArgs), IdName(dt), typeParams);
        DatatypeFieldsAndConstructor(ctor, constructorIndex, wr);
        constructorIndex++;
      }
    }

    void DatatypeFieldsAndConstructor(DatatypeCtor ctor, int constructorIndex, TargetWriter wr) {
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
          wr.WriteLine("public readonly {0} {1};", TypeName(arg.Type, wr, arg.tok), FormalName(arg, i));
          i++;
        }
      }

      wr.Write("public {0}(", DtCtorDeclarationName(ctor));
      WriteFormals("", ctor.Formals, wr);
      using (var w = wr.NewBlock(")")) {
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine("this.{0} = {0};", FormalName(arg, i));
            i++;
          }
        }
      }

      if (dt is CoDatatypeDecl) {
        string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
        wr.WriteLine("public override {0}{1} _Get() {{ return this; }}", dt.CompileName, typeParams);
      }

      // Equals method
      using (var w = wr.NewBlock("public override bool Equals(object other)")) {
        w.Write("var oth = other as {0}", DtCtorName(ctor, dt.TypeArgs));
        w.WriteLine(";");
        w.Write("return oth != null");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            if (IsDirectlyComparable(arg.Type)) {
              w.Write(" && this.{0} == oth.{0}", nm);
            } else {
              w.Write(" && Dafny.Helpers.AreEqual(this.{0}, oth.{0})", nm);
            }
            i++;
          }
        }
        w.WriteLine(";");
      }

      // GetHashCode method (Uses the djb2 algorithm)
      using (var w = wr.NewBlock("public override int GetHashCode()")) {
        w.WriteLine("ulong hash = 5381;");
        w.WriteLine("hash = ((hash << 5) + hash) + {0};", constructorIndex);
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            w.WriteLine("hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.{0}));", nm);
            i++;
          }
        }
        w.WriteLine("return (int) hash;");
      }

      using (var w = wr.NewBlock("public override string ToString()")) {
        string nm;
        if (dt is TupleTypeDecl) {
          nm = "";
        } else {
          nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
        }
        if (dt is TupleTypeDecl tupleDt && ctor.Formals.Count == 0) {
          // here we want parentheses and no name
          w.WriteLine("return \"()\";");
        } else if (dt is CoDatatypeDecl) {
          w.WriteLine("return \"{0}\";", nm);
        } else {
          var tempVar = GenVarName("s", ctor.Formals);
          w.WriteLine("string {0} = \"{1}\";", tempVar, nm);
          if (ctor.Formals.Count != 0) {
            w.WriteLine("{0} += \"(\";", tempVar);
            i = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                if (i != 0) {
                  w.WriteLine("{0} += \", \";", tempVar);
                }
                w.WriteLine("{0} += Dafny.Helpers.ToString(this.{1});", tempVar, FormalName(arg, i));
                i++;
              }
            }
            w.WriteLine("{0} += \")\";", tempVar);
          }
          w.WriteLine("return {0};", tempVar);
        }
      }
    }

    /// <summary>
    /// Returns a protected name with type parameters.
    /// </summary>
    string DtCtorDeclarationName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorDeclarationName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
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
    string DtCtorName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
    }
    /// <summary>
    /// Returns a protected name with type parameters.
    /// </summary>
    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs, TextWriter wr) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeArgs != null && typeArgs.Count != 0) {
        s += "<" + TypeNames(typeArgs, wr, ctor.tok) + ">";
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
      var dtName = dt.Module.IsDefaultModule ? IdProtect(dt.CompileName) : dt.FullCompileName;
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }
    string DtCreateName(DatatypeCtor ctor) {
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      } else {
        return "create_" + ctor.CompileName;
      }
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr) {
      var cw = CreateClass(IdName(nt), null, wr) as CsharpCompiler.ClassWriter;
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var wEnum = w.NewNamedBlock("public static System.Collections.Generic.IEnumerable<{0}> IntegerRange(BigInteger lo, BigInteger hi)", GetNativeTypeName(nt.NativeType));
        wEnum.WriteLine("for (var j = lo; j < hi; j++) {{ yield return ({0})j; }}", GetNativeTypeName(nt.NativeType));
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(nt.Witness, witness, false);
        if (nt.NativeType == null) {
          cw.DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString());
        } else {
          w.Write("public static readonly {0} Witness = ({0})(", GetNativeTypeName(nt.NativeType));
          w.Append(witness);
          w.WriteLine(");");
        }
      }
      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr) {
      ClassWriter cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as ClassWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var sw = new TargetWriter(cw.InstanceMemberWriter.IndentLevel, true);
        TrExpr(sst.Witness, sw, false);
        cw.DeclareField("Witness", true, true, sst.Rhs, sst.tok, sw.ToString());
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      if (sel == NativeType.Selection.Number) {
        sel = NativeType.Selection.Long;
      }
      base.GetNativeInfo(sel, out name, out literalSuffix, out needsCastAfterArithmetic);
    }

    protected class ClassWriter : IClassWriter {
      public readonly CsharpCompiler Compiler;
      public readonly BlockTargetWriter InstanceMemberWriter;
      public readonly BlockTargetWriter StaticMemberWriter;

      public ClassWriter(CsharpCompiler compiler, BlockTargetWriter instanceMemberWriter, BlockTargetWriter staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.StaticMemberWriter = staticMemberWriter == null ? instanceMemberWriter : staticMemberWriter;
      }

      public BlockTargetWriter Writer(bool isStatic) {
        return isStatic ? StaticMemberWriter : InstanceMemberWriter;
      }

      public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
        return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
      }
      public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
      }
      public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic));
      }
      public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic));
      }
      public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, Writer(isStatic));
      }
      public TextWriter/*?*/ ErrorWriter() => InstanceMemberWriter;

      public void Finish() { }
    }

    protected BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, TargetWriter wr) {
      var hasDllImportAttribute = ProcessDllImport(m, wr);
      string targetReturnTypeReplacement = null;
      foreach (var p in m.Outs) {
        if (!p.IsGhost) {
          if (targetReturnTypeReplacement == null) {
            targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
          } else if (targetReturnTypeReplacement != null) {
            // there's more than one out-parameter, so bail
            targetReturnTypeReplacement = null;
            break;
          }
        }
      }

      var customReceiver = NeedsCustomReceiver(m);

      wr.Write("{0}{1}{2}{3} {4}",
        createBody ? "public " : "",
        m.IsStatic || customReceiver ? "static " : "",
        hasDllImportAttribute ? "extern " : "",
        targetReturnTypeReplacement ?? "void",
        IdName(m));
      if (m.TypeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(m.TypeArgs));
      }
      wr.Write("(");
      int nIns;
      if (customReceiver) {
        var nt = m.EnclosingClass;
        var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, nt);
        DeclareFormal("", "_this", receiverType, m.tok, true, wr);
        nIns = 1;
      } else {
        nIns = 0;
      }
      nIns += WriteFormals(nIns == 0 ? "" : ", ", m.Ins, wr);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wr);
      }

      if (!createBody || hasDllImportAttribute) {
        wr.WriteLine(");");
        return null;
      } else {
        var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        if (m.IsTailRecursive) {
          if (!m.IsStatic && !customReceiver) {
            w.WriteLine("var _this = this;");
          }
          w.IndentLess(); w.WriteLine("TAIL_CALL_START: ;");
        }

        if (targetReturnTypeReplacement != null) {
          var r = new TargetWriter(w.IndentLevel);
          EmitReturn(m.Outs, r);
          w.BodySuffix = r.ToString();
        }
        return w;
      }
    }

    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, TargetWriter wr) {
      var hasDllImportAttribute = ProcessDllImport(member, wr);

      var customReceiver = NeedsCustomReceiver(member);

      wr.Write("{0}{1}{2}{3} {4}", createBody ? "public " : "", isStatic || customReceiver ? "static " : "", hasDllImportAttribute ? "extern " : "", TypeName(resultType, wr, tok), name);
      if (typeArgs != null && typeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(typeArgs));
      }
      wr.Write("(");
      if (customReceiver) {
        var nt = member.EnclosingClass;
        var receiverType = UserDefinedType.FromTopLevelDecl(tok, nt);
        DeclareFormal("", "_this", receiverType, tok, true, wr);
      }
      WriteFormals(customReceiver ? ", " : "", formals, wr);
      if (!createBody || hasDllImportAttribute) {
        wr.WriteLine(");");
        return null;
      } else {
        if (formals.Count > 1) {
          var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
          return w;
        } else {
          var w = wr.NewBlock(")");
          return w;
        }
      }
    }

    protected BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr) {
      wr.Write("{0}{1}{2} {3} {{ get", createBody ? "public " : "", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (createBody) {
        var w = wr.NewBlock("", " }");
        return w;
      } else {
        wr.WriteLine("; }");
        return null;
      }
    }

    protected BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      wr.Write("{0}{1}{2} {3}", createBody ? "public " : "", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (createBody) {
        var w = wr.NewBlock("");
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
    public bool ProcessDllImport(MemberDecl decl, TargetWriter wr) {
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

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("goto TAIL_CALL_START;");
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
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
        string typeNameSansBrackets, brackets;
        TypeName_SplitArrayName(elType, wr, tok, out typeNameSansBrackets, out brackets);
        return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets;
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
        return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">";
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
        return DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok, bool inAutoInitContext) {
      var xType = type.NormalizeExpandKeepConstraints();

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigInteger.Zero";
      } else if (xType is RealType) {
        return "Dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "BigInteger.Zero";
      } else if (xType is CollectionType) {
        return TypeName(xType, wr, tok) + ".Empty";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        return "Dafny.Helpers.Default<" + TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ">()";
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
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return string.Format("(({0})null)", TypeName(xType, wr, udt.tok));
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("(({0}) => {1})",
              Util.Comma(", ", udt.TypeArgs.Count - 1, i => string.Format("{0} x{1}", TypeName(udt.TypeArgs[i], wr, udt.tok), i)),
              rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            string typeNameSansBrackets, brackets;
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out typeNameSansBrackets, out brackets);
            return string.Format("new {0}[{1}]{2}", typeNameSansBrackets, Util.Comma(arrayClass.Dims, _ => "0"), brackets);
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return string.Format("default({0})", TypeName(xType, wr, udt.tok));
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return string.Format("({0})null", TypeName(xType, wr, udt.tok));
        }
      } else if (cl is DatatypeDecl) {
        var s = FullTypeName(udt);
        var rc = cl;
        if (DafnyOptions.O.IronDafny &&
            !(xType is ArrowType) &&
            rc != null &&
            rc.Module != null &&
            !rc.Module.IsDefaultModule) {
          s = "@" + rc.FullCompileName;
        }
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs, wr, udt.tok) + ">";
        }
        return string.Format("{0}.Default", s);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0) {
        if (typeArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += "<" + TypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member) {
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is TraitDecl) {
        string s = udt.FullCompanionCompileName;
        Contract.Assert(udt.TypeArgs.Count == 0);  // traits have no type parameters
        return s;
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    // ----- Declarations -------------------------------------------------------------

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      wr.WriteLine("public {3}{4}{0} {1} = {2};", TypeName(type, wr, tok), name, rhs,
        isStatic ? "static " : "",
        isConst ? "readonly " : "");
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      wr.Write("{0}{1}{2} {3}", prefix, isInParam ? "" : "out ", TypeName(type, wr, tok), name);
      return true;
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, bool leaveRoomForRhs, string/*?*/ rhs, TargetWriter wr) {
      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "var", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null);  // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken/*?*/ tok, TargetWriter wr) {
      wr.Write("{0} {1} = ", type != null ? TypeName(type, wr, tok) : "var", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("var {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr) {
      if (useReturnStyleOuts) {
        DeclareLocalVar(name, type, tok, false, rhs, wr);
      } else {
        EmitAssignment(name, type, rhs, null, wr);
      }
    }

    protected override void EmitActualOutArg(string actualOutParamName, TextWriter wr) {
      wr.Write("out {0}", actualOutParamName);
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) {
      return nonGhostOutCount == 1;
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      Contract.Assert(actualOutParamNames.Count == 1);
      EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      if (typeArgs.Count != 0) {
        wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
      }
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return (type != null ? TypeName(type, wr, tok) : "var") + " " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Write("Dafny.Helpers.Print(");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (outParams.Count == 1) {
        wr.WriteLine("return {0};", IdName(outParams[0]));
      } else {
        wr.WriteLine("return;");
      }
    }

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      var w = wr.ForkSection();
      wr.IndentLess();
      wr.WriteLine("after_{0}: ;", label);
      return w;
    }

    protected override void EmitBreak(string/*?*/ label, TargetWriter wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("goto after_{0};", label);
      }
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.WriteLine("yield return null;");
    }

    protected override void EmitAbsurd(string/*?*/ message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw new System.Exception(\"{0}\");", message);
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock("for (var {0} = 0; {0} < {1}; {0}++)", indexVar, bound);
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock("for (var {0} = new BigInteger({1}); ; {0} *= 2)", indexVar, start);
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0}++;", varName);
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine("{0}--;", varName);
    }

    protected override string GetQuantifierName(string bvType) {
      return string.Format("Dafny.Helpers.Quantifier<{0}>", bvType);
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type/*?*/ boundVarType, out TargetWriter collectionWriter, TargetWriter wr, string/*?*/ altBoundVarName = null, Type/*?*/ altVarType = null, Bpl.IToken/*?*/ tok = null) {
      wr.Write("foreach (var {0} in ", boundVar);
      collectionWriter = wr.Fork();
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      } else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", "{0} = {1};", altBoundVarName, boundVar);
      } else {
        return wr.NewBlockWithPrefix(")", "{2} {0} = ({2}){1};", altBoundVarName, boundVar, TypeName(altVarType, wr, tok));
      }
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      var ctor = initCall == null ? null : (Constructor)initCall.Method;  // correctness of cast follows from precondition of "EmitNew"
      wr.Write("new {0}(", TypeName(type, wr, tok));
      string q, n;
      if (ctor != null && ctor.IsExtern(out q, out n)) {
        // the arguments of any external constructor are placed here
        string sep = "";
        for (int i = 0; i < ctor.Ins.Count; i++) {
          Formal p = ctor.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(initCall.Args[i], wr, false);
            sep = ", ";
          }
        }
      }
      wr.Write(")");
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      if (!mustInitialize || HasSimpleZeroInitializer(elmtType)) {
        string typeNameSansBrackets, brackets;
        TypeName_SplitArrayName(elmtType, wr, tok, out typeNameSansBrackets, out brackets);
        wr.Write("new {0}", typeNameSansBrackets);
        string prefix = "[";
        foreach (var dim in dimensions) {
          wr.Write("{0}(int)", prefix);
          TrParenExpr(dim, wr, false);
          prefix = ", ";
        }
        wr.Write("]{0}", brackets);
      } else {
        wr.Write("Dafny.ArrayHelpers.InitNewArray{0}<{1}>", dimensions.Count, TypeName(elmtType, wr, tok));
        wr.Write("(");
        wr.Write(DefaultValue(elmtType, wr, tok));
        foreach (var dim in dimensions) {
          wr.Write(", ");
          TrParenExpr(dim, wr, false);
        }
        wr.Write(")");
      }
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
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
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("{0}<char>.FromString(", DafnySeqClass);
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) != null) {
        string nativeName = null, literalSuffix = null;
        bool needsCastAfterArithmetic = false;
        GetNativeInfo(AsNativeType(e.Type).Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
        wr.Write((BigInteger)e.Value + literalSuffix);
      } else if (e.Value is BigInteger) {
        var i = (BigInteger)e.Value;
        EmitIntegerLiteral(i, wr);
      } else if (e.Value is Basetypes.BigDec) {
        var n = (Basetypes.BigDec)e.Value;
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
    void EmitIntegerLiteral(BigInteger i, TextWriter wr) {
      Contract.Requires(wr != null);
      if (i.IsZero) {
        wr.Write("BigInteger.Zero");
      } else if (i.IsOne) {
        wr.Write("BigInteger.One");
      } else if (int.MinValue <= i && i <= int.MaxValue) {
          wr.Write("new BigInteger({0})", i);
      } else if (long.MinValue <= i && i <= long.MaxValue) {
        wr.Write("new BigInteger({0}L)", i);
      } else if (ulong.MinValue <= i && i <= ulong.MaxValue) {
        wr.Write("new BigInteger({0}UL)", i);
      } else {
        wr.Write("BigInteger.Parse(\"{0}\")", i);
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      wr.Write("{0}\"{1}\"", isVerbatim ? "@" : "", str);
    }

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      // --- Before
      if (bvType.NativeType == null) {
        wr.Write("((");
      } else {
        if (surroundByUnchecked) {
          // Unfortunately, the following will apply "unchecked" to all subexpressions as well.  There
          // shouldn't ever be any problem with this, but stylistically it would have been nice to have
          // applied the "unchecked" only to the actual operation that may overflow.
          wr.Write("unchecked(");
        }
        wr.Write("({0})((", nativeName);
      }
      // --- Middle
      var middle = wr.Fork();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write(") & ((new BigInteger(1) << {0}) - 1))", bvType.Width);
      } else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          wr.Write(") & ({2})0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix, nativeName);
        } else {
          wr.Write("))");  // close the parentheses for the cast
        }
        if (surroundByUnchecked) {
          wr.Write(")");  // close the parentheses for the "unchecked"
        }
      }

      return middle;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      // ( e0 op1 e1) | (e0 op2 (width - e1))
      if (needsCast) {
        wr.Write("(" + nativeName + ")(");
      }
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, nativeType, true, wr, inLetExprBody, tr);
      wr.Write(")");

      wr.Write (" | ");

      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, nativeType, false, wr, inLetExprBody, tr);
      wr.Write(")");

      if (needsCast) {
        wr.Write(")");
      }
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType/*?*/ nativeType, bool firstOp, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody);
      wr.Write(" {0} ", op);
      if (!firstOp) {
        wr.Write("({0} - ", bv.Width);
      }

      wr.Write("(int)(");
      tr(e1, wr, inLetExprBody);
      wr.Write(")");

      if (!firstOp) {
        wr.Write(")");
      }
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr) {
      wr.Write("new System.Collections.Generic.List<System.Tuple<{0}>>()", tupleTypeArgs);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      wr.Write("{0}.Add(new System.Tuple<{1}>(", ingredients, tupleTypeArgs);
      var wrTuple = wr.Fork();
      wr.WriteLine("));");
      return wrTuple;
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write("{0}.Item{1}", prefix, i+1);
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
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      } else if (cl.Module.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      } else {
        return IdProtect(cl.Module.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override void EmitThis(TargetWriter wr) {
      var custom =
        (enclosingMethod != null && enclosingMethod.IsTailRecursive) ||
        thisContext is NewtypeDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.Module.IsDefaultModule ? dt.CompileName : dt.FullCompileName;
      var ctorName = dtv.Ctor.CompileName;

      var typeParams = dtv.InferredTypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeNames(dtv.InferredTypeArgs, wr, dtv.tok));
      if (!dtv.IsCoCall) {
        wr.Write("@{0}{1}.", dtName, typeParams);
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   new Dt_Cons<T>( args )
        wr.Write("{0}({1})", DtCreateName(dtv.Ctor), arguments);
      } else {
        // In the case of a co-recursive call, generate:
        //     new Dt__Lazy<T>( LAMBDA )
        // where LAMBDA is:
        //     () => { return Dt_Cons<T>( ...args... ); }
        wr.Write("new {0}__Lazy{1}(", dtv.DatatypeName, typeParams);

        wr.Write("() => { return ");
        wr.Write("new {0}({1})", DtCtorName(dtv.Ctor, dtv.InferredTypeArgs, wr), arguments);
        wr.Write("; })");
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
          compiledName = idParam == null ? "Length" : "GetLength(" + (int)idParam + ")";
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

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr) {
      var wSource = wr.Fork();
      if (isLValue && member is ConstantField) {
        wr.Write("._{0}", member.CompileName);
      } else if (!isLValue && member is SpecialField sf) {
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
      return wSource;
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
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

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
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

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr("(int)", expr, wr, inLetExprBody);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(source, wr, inLetExprBody);
      TrParenExpr(".Select", index, wr, inLetExprBody);
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody, TargetWriter wr, bool nativeIndex = false) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".Update(");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitSeqSelectRange(Expression source, Expression/*?*/ lo, Expression/*?*/ hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        wr.Write("Dafny.Helpers.SeqFromArray");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (hi != null) {
        TrParenExpr(".Take", hi, wr, inLetExprBody);
      }
      if (lo != null) {
        TrParenExpr(".Drop", lo, wr, inLetExprBody);
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr) {
      wr.Write("{0}<{1}>.Create(", DafnySeqClass, TypeName(expr.Type.AsSeqType.Arg, wr, expr.tok));
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
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

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr) {
      wr.Write("Dafny.Helpers.Id<");
      wr.Write(TypeName(functionType, wr, tok));
      wr.Write(">(");
      TrExpr(function, wr, inLetExprBody);
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs, List<Type> boundTypes, Type resultType, Bpl.IToken tok, bool inLetExprBody, TargetWriter wr) {
      wr.Write("Dafny.Helpers.Id<{0}>(({1}) => ", typeArgs, Util.Comma(boundVars));
      var w = wr.Fork();
      wr.Write(")");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr) {
      var dtorName = FormalName(dtor, formalNonGhostIndex);
      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source, ctor.EnclosingDatatype is CoDatatypeDecl ? "._Get()" : "", dtorName);
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      // (
      //   (System.Func<inTypes,resultType>)  // cast, which tells C# what the various types involved are
      //   (
      //     (inNames) => {
      //       <<caller fills in body here; must end with a return statement>>
      //     }
      //   )
      // )
      wr.Write('(');
      if (!untyped) {
        wr.Write("(System.Func<{0}{1}>)", Util.Comma("", inTypes, t => TypeName(t, wr, tok) + ", "), TypeName(resultType, wr, tok));
      }
      wr.Write("(({0}) =>", Util.Comma(inNames, nm => nm));
      var w = wr.NewBigExprBlock("", "))");
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write("Dafny.Helpers.Let<{0},{1}>(", TypeName(sourceType, wr, sourceTok), TypeName(resultType, wr, resultTok));
      TrExpr(source, wr, inLetExprBody);
      wr.Write(", {0} => ", bvName);
      var w = wr.Fork();
      wr.Write(")");
      int y = ((System.Func<int,int>)((u) => u + 5))(6);
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write("Dafny.Helpers.Let<{0},{1}>(", TypeName(sourceType, wr, sourceTok), TypeName(resultType, wr, resultTok));
      wr.Write("{0}, {1} => ", source, bvName);
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      // (
      //   (System.Func<resultType>)(() => <<body>>)
      // )()
      wr.Write("((System.Func<{0}>)(() =>", TypeName(resultType, wr, resultTok));
      var w = wr.NewBigExprBlock("", "))()");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write("Dafny.Helpers.Let<int,{0}>(", TypeName(resultType, wr, resultTok));
      wr.Write("{0}, {1} => ", source, bvName);
      var w = wr.NewBigExprBlock("", ")");
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
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
          opString = "&"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          opString = "|"; break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          opString = "^"; break;

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
              callString = "Equals";
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
              callString = "Equals";
            }
            break;
          }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<"; break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<="; break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">="; break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">"; break;
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
            staticCallString = "Dafny.Helpers.EuclideanDivision" + suffix;
          } else {
            opString = "/";  // for reals
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = "Dafny.Helpers.EuclideanModulus" + suffix;
          } else {
            opString = "%";  // for reals
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "Equals"; break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
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
          callString = "Intersect"; break;
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
      wr.Write("{0} == 0", varName);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("new Dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("new BigInteger");
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(", BigInteger.One)");
        } else if (e.ToType.IsCharType) {
          wr.Write("(char)(");
          TrExpr(e.E, wr, inLetExprBody);
          wr.Write(")");
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
            string toNativeName, toNativeSuffix;
            bool toNativeNeedsCast;
            GetNativeInfo(toNative.Sel, out toNativeName, out toNativeSuffix, out toNativeNeedsCast);
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
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else {
          // real -> (int or bv)
          if (AsNativeType(e.ToType) != null) {
            wr.Write("({0})", GetNativeTypeName(AsNativeType(e.ToType)));
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".ToBigInteger()");
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
        // identity will do
        TrExpr(e.E, wr, inLetExprBody);
      }
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("{0}.FromElements", TypeName(ct, wr, tok));
      TrExprList(elements, wr, inLetExprBody);
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("{0}.FromElements", TypeName(mt, wr, tok));
      wr.Write("(");
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("new Dafny.Pair<");
        wr.Write(TypeName(p.A.Type, wr, p.A.tok));
        wr.Write(",");
        wr.Write(TypeName(p.B.Type, wr, p.B.tok));
        wr.Write(">(");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(",");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write(")");
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("new System.Collections.Generic.List<{0}>()", TypeName(ct.Arg, wr, tok));
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
        wr.Write("new System.Collections.Generic.List<Dafny.Pair<{0},{1}>>()", domtypeName, rantypeName);
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("{0}.Add(", collName);
        TrExpr(elmt, wr, inLetExprBody);
        wr.WriteLine(");");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr) {
      var domtypeName = TypeName(mt.Domain, wr, tok);
      var rantypeName = TypeName(mt.Range, wr, tok);
      wr.Write("{0}.Add(new Dafny.Pair<{1},{2}>(", collName, domtypeName, rantypeName);
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine("));");
      return termLeftWriter;
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      if (ct is SetType) {
        var typeName = TypeName(ct.Arg, wr, tok);
        return string.Format("Dafny.Set<{0}>.FromCollection({1})", typeName, collName);
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
        return string.Format("{3}<{0},{1}>.FromCollection({2})", domtypeName, rantypeName, collName, DafnyMapClass);
      } else {
        Contract.Assume(false);  // unepxected collection type
        throw new cce.UnreachableException();  // please compiler
      }
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      wr.Write("Dafny.Helpers.SingleValue<{0}>", type);
      TrParenExpr(e, wr, inLetExprBody);
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    private class CSharpCompilationResult
    {
      public string libPath;
      public List<string> immutableDllFileNames;
      public CompilerResults cr;
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {

      compilationResult = null;

      if (!CodeDomProvider.IsDefinedLanguage("CSharp")) {
        outputWriter.WriteLine("Error: cannot compile, because there is no provider configured for input language CSharp");
        return false;
      }

      var provider = CodeDomProvider.CreateProvider("CSharp", new Dictionary<string, string> { { "CompilerVersion", "v4.0" } });
      var cp = new System.CodeDom.Compiler.CompilerParameters();
      cp.GenerateExecutable = hasMain;
      if (DafnyOptions.O.RunAfterCompile) {
        cp.GenerateInMemory = true;
      } else if (hasMain) {
        cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "exe");
        cp.GenerateInMemory = false;
      } else {
        cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "dll");
        cp.GenerateInMemory = false;
      }
      // The nowarn numbers are the following:
      // * CS0164 complains about unreferenced labels
      // * CS0219/CS0168 is about unused variables
      // * CS1717 is about assignments of a variable to itself
      // * CS0162 is about unreachable code
      cp.CompilerOptions = "/debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168";
      cp.ReferencedAssemblies.Add("System.Numerics.dll");
      cp.ReferencedAssemblies.Add("System.Core.dll");
      cp.ReferencedAssemblies.Add("System.dll");

      var crx = new CSharpCompilationResult();
      crx.libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location) + Path.DirectorySeparatorChar;
      if (DafnyOptions.O.UseRuntimeLib) {
        cp.ReferencedAssemblies.Add(crx.libPath + "DafnyRuntime.dll");
      }

      crx.immutableDllFileNames = new List<string>() {
        "System.Collections.Immutable.dll",
        "System.Runtime.dll",
        "netstandard.dll"
      };

      if (DafnyOptions.O.Optimize) {
        cp.CompilerOptions += " /optimize /define:DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE";
        cp.CompilerOptions += " /lib:" + crx.libPath;
        foreach (var filename in crx.immutableDllFileNames) {
          cp.ReferencedAssemblies.Add(filename);
        }
      }

      int numOtherSourceFiles = 0;
      if (otherFileNames.Count > 0) {
        foreach (var file in otherFileNames) {
          string extension = Path.GetExtension(file);
          if (extension != null) { extension = extension.ToLower(); }
          if (extension == ".cs") {
            numOtherSourceFiles++;
          } else if (extension == ".dll") {
            cp.ReferencedAssemblies.Add(Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file)));
          }
        }
      }

      if (numOtherSourceFiles > 0) {
        string[] sourceFiles = new string[numOtherSourceFiles + 1];
        sourceFiles[0] = targetFilename;
        int index = 1;
        foreach (var file in otherFileNames) {
          string extension = Path.GetExtension(file);
          if (extension != null) { extension = extension.ToLower(); }
          if (extension == ".cs") {
            var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
            if (File.Exists(normalizedPath)) {
              sourceFiles[index++] = normalizedPath;
            } else {
              outputWriter.WriteLine("Errors compiling program: Could not find {0}", file);
              return false;
            }
          }
        }
        crx.cr = provider.CompileAssemblyFromFile(cp, sourceFiles);
      } else {
        crx.cr = provider.CompileAssemblyFromSource(cp, targetProgramText);
      }

      if (crx.cr.Errors.Count != 0) {
        if (cp.GenerateInMemory) {
          outputWriter.WriteLine("Errors compiling program");
        } else {
          var assemblyName = Path.GetFileName(crx.cr.PathToAssembly);
          outputWriter.WriteLine("Errors compiling program into {0}", assemblyName);
        }
        foreach (var ce in crx.cr.Errors) {
          outputWriter.WriteLine(ce.ToString());
          outputWriter.WriteLine();
        }
        return false;
      }

      if (!cp.GenerateInMemory) {
        var assemblyName = Path.GetFileName(crx.cr.PathToAssembly);
        if (DafnyOptions.O.CompileVerbose) {
          outputWriter.WriteLine("Compiled assembly into {0}", assemblyName);
        }
        if (DafnyOptions.O.Optimize) {
          var outputDir = Path.GetDirectoryName(dafnyProgramName);
          if (string.IsNullOrWhiteSpace(outputDir)) {
            outputDir = ".";
          }
          foreach (var filename in crx.immutableDllFileNames) {
            var destPath = outputDir + Path.DirectorySeparatorChar + filename;
            File.Copy(crx.libPath + filename, destPath, true);
            if (DafnyOptions.O.CompileVerbose) {
              outputWriter.WriteLine("Copied /optimize dependency {0} to {1}", filename, outputDir);
            }
          }
        }
      }

      compilationResult = crx;
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      var crx = (CSharpCompilationResult)compilationResult;
      var cr = crx.cr;

      var assemblyName = Path.GetFileName(cr.PathToAssembly);
      var entry = cr.CompiledAssembly.EntryPoint;
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
  }
}
