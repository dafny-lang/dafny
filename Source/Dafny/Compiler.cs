//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using System.Text;

namespace Microsoft.Dafny {
  public class Compiler {
    public Compiler(TextWriter wr) {
      Contract.Requires(wr != null);
      this.wr = wr;
    }

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(wr!=null);
    }

    TextWriter wr;
    Method enclosingMethod;  // non-null when a method body is being translated
    internal static IUniqueNameGenerator UniqueNameGeneratorSingleton = new UniqueNameGenerator();

    class UniqueNameGenerator : IUniqueNameGenerator
    {
      int nameCount;
      public int GenerateId(string name)
      {
        return nameCount++;
      }
    }

    Dictionary<Expression, int> uniqueAstNumbers = new Dictionary<Expression, int>();
    int GetUniqueAstNumber(Expression expr) {
      Contract.Requires(expr != null);
      int n;
      if (!uniqueAstNumbers.TryGetValue(expr, out n)) {
        n = uniqueAstNumbers.Count;
        uniqueAstNumbers.Add(expr, n);
      }
      return n;
    }

    public int ErrorCount;
    void Error(string msg, params object[] args) {
      Contract.Requires(msg != null);
      Contract.Requires(args != null);

      string s = string.Format("Compilation error: " + msg, args);
      Console.WriteLine(s);
      wr.WriteLine("/* {0} */", s);
      ErrorCount++;
    }

    void ReadRuntimeSystem() {
      string codebase = cce.NonNull( System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
      string path = System.IO.Path.Combine(codebase, "DafnyRuntime.cs");
      using (TextReader rd = new StreamReader(new FileStream(path, System.IO.FileMode.Open, System.IO.FileAccess.Read)))
      {
        while (true) {
          string s = rd.ReadLine();
          if (s == null)
            return;
          wr.WriteLine(s);
        }
      }
    }

    readonly int IndentAmount = 2;
    void Indent(int ind) {
      Contract.Requires(0 <= ind);
      string spaces = "          ";
      for (; spaces.Length < ind; ind -= spaces.Length) {
        wr.Write(spaces);
      }
      wr.Write(spaces.Substring(0, ind));
    }

    public void Compile(Program program) {
      Contract.Requires(program != null);
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine();
      ReadRuntimeSystem();
      CompileBuiltIns(program.BuiltIns);

      foreach (ModuleDefinition m in program.CompileModules) {
        if (m.IsAbstract) {
          // the purpose of an abstract module is to skip compilation
          continue;
        }
        int indent = 0;
        if (!m.IsDefaultModule) {
          wr.WriteLine("namespace @{0} {{", m.CompileName);
          indent += IndentAmount;
        }
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          wr.WriteLine();
          if (d is ArbitraryTypeDecl) {
            var at = (ArbitraryTypeDecl)d;
            Error("Arbitrary type ('{0}') cannot be compiled", at.FullName);
          } else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            Indent(indent);
            wr.Write("public abstract class Base_{0}", dt.CompileName);
            if (dt.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
            }
            wr.WriteLine(" { }");
            CompileDatatypeConstructors(dt, indent);
            CompileDatatypeStruct(dt, indent);
          } else if (d is IteratorDecl) {
            var iter = (IteratorDecl)d;
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
            //     public void MoveNext(out bool more) {
            //       more =_iter.MoveNext();
            //     }
            //   
            //     private IEnumerator<object> TheIterator() {
            //       // the translation of the body of the iterator, with each "yield" turning into a "yield return null;"
            //       yield break;
            //     }
            //   }

            Indent(indent);
            wr.Write("public class @{0}", iter.CompileName);
            if (iter.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(iter.TypeArgs));
            }
            wr.WriteLine(" {");
            var ind = indent + IndentAmount;
            // here come the fields
            Constructor ct = null;
            foreach (var member in iter.Members) {
              var f = member as Field;
              if (f != null && !f.IsGhost) {
                Indent(ind);
                wr.WriteLine("public {0} @{1} = {2};", TypeName(f.Type), f.CompileName, DefaultValue(f.Type));
              } else if (member is Constructor) {
                Contract.Assert(ct == null);  // we're expecting just one constructor
                ct = (Constructor)member;
              }
            }
            Contract.Assert(ct != null);  // we do expect a constructor
            Indent(ind); wr.WriteLine("System.Collections.Generic.IEnumerator<object> __iter;");

            // here's the initializer method
            Indent(ind); wr.Write("public void @{0}(", ct.CompileName);
            string sep = "";
            foreach (var p in ct.Ins) {
              if (!p.IsGhost) {
                // here we rely on the parameters and the corresponding fields having the same names
                wr.Write("{0}{1} @{2}", sep, TypeName(p.Type), p.CompileName);
                sep = ", ";
              }
            }
            wr.WriteLine(") {");
            foreach (var p in ct.Ins) {
              if (!p.IsGhost) {
                Indent(ind + IndentAmount);
                wr.WriteLine("this.@{0} = @{0};", p.CompileName);
              }
            }
            Indent(ind + IndentAmount); wr.WriteLine("__iter = TheIterator();");
            Indent(ind);  wr.WriteLine("}");
            // here are the enumerator methods
            Indent(ind); wr.WriteLine("public void MoveNext(out bool more) { more = __iter.MoveNext(); }");
            Indent(ind); wr.WriteLine("private System.Collections.Generic.IEnumerator<object> TheIterator() {");
            if (iter.Body == null) {
              Error("Iterator {0} has no body", iter.FullName);
            } else {
              TrStmt(iter.Body, ind + IndentAmount);
            }
            Indent(ind + IndentAmount); wr.WriteLine("yield break;");
            Indent(ind); wr.WriteLine("}");
            // end of the class
            Indent(indent); wr.WriteLine("}");

          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            Indent(indent);
            wr.Write("public class @{0}", cl.CompileName);
            if (cl.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(cl.TypeArgs));
            }
            wr.WriteLine(" {");
            CompileClassMembers(cl, indent+IndentAmount);
            Indent(indent);  wr.WriteLine("}");
          } else if (d is ModuleDecl) {
            // nop
          } else { Contract.Assert(false); }
        }
        if (!m.IsDefaultModule) {
          wr.WriteLine("}} // end of namespace {0}", m.CompileName);
        }
      }
    }

    void CompileBuiltIns(BuiltIns builtIns) {
      wr.WriteLine("namespace Dafny {");
      Indent(IndentAmount);
      wr.WriteLine("public partial class Helpers {");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl) {
          int dims = ((ArrayClassDecl)decl).Dims;
          // public static T[,] InitNewArray2<T>(BigInteger size0, BigInteger size1) {
          Indent(3 * IndentAmount);
          wr.Write("public static T[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] InitNewArray{0}<T>(", dims);
          RepeatWrite(wr, dims, "BigInteger size{0}", ", ");
          wr.WriteLine(") {");
          // int s0 = (int)size0;
          for (int i = 0; i < dims; i++) {
            Indent(4 * IndentAmount);
            wr.WriteLine("int s{0} = (int)size{0};", i);
          }
          // T[,] a = new T[s0, s1];
          Indent(4 * IndentAmount);
          wr.Write("T[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] a = new T[");
          RepeatWrite(wr, dims, "s{0}", ",");
          wr.WriteLine("];");
          // BigInteger[,] b = a as BigInteger[,];
          Indent(4 * IndentAmount);
          wr.Write("BigInteger[");
          RepeatWrite(wr, dims, "", ",");
          wr.Write("] b = a as BigInteger[");
          RepeatWrite(wr, dims, "", ",");
          wr.WriteLine("];");
          // if (b != null) {
          Indent(4 * IndentAmount);
          wr.WriteLine("if (b != null) {");
          // BigInteger z = new BigInteger(0);
          Indent(5 * IndentAmount);
          wr.WriteLine("BigInteger z = new BigInteger(0);");
          // for (int i0 = 0; i0 < s0; i0++)
          //   for (int i1 = 0; i1 < s1; i1++)
          for (int i = 0; i < dims; i++) {
            Indent((5+i) * IndentAmount);
            wr.WriteLine("for (int i{0} = 0; i{0} < s{0}; i{0}++)", i);
          }
          // b[i0,i1] = z;
          Indent((5+dims) * IndentAmount);
          wr.Write("b[");
          RepeatWrite(wr, dims, "i{0}", ",");
          wr.WriteLine("] = z;");
          // }
          Indent(4 * IndentAmount);
          wr.WriteLine("}");
          // return a;
          Indent(4 * IndentAmount);
          wr.WriteLine("return a;");
          // }
          Indent(3 * IndentAmount);
          wr.WriteLine("}");  // end of method
        }
      }
      Indent(IndentAmount);
      wr.WriteLine("}");  // end of class Helpers
      wr.WriteLine("}");  // end of namespace
    }

    static void RepeatWrite(TextWriter wr, int times, string template, string separator) {
      Contract.Requires(1 <= times);
      string s = "";
      for (int i = 0; i < times; i++) {
        wr.Write(s);
        wr.Write(template, i);
        s = separator;
      }
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, int indent)
    {
      Contract.Requires(dt != null);

      string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
      if (dt is CoDatatypeDecl) {
        // public class Dt__Lazy<T> : Base_Dt<T> {
        //   public delegate Base_Dt<T> Computer();
        //   public delegate Computer ComputerComputer();
        //   Computer c;
        //   public Dt__Lazy(Computer c) { this.c = c; }
        //   public Base_Dt<T> Get() { return c(); }
        // }
        Indent(indent);
        wr.WriteLine("public class {0}__Lazy{1} : Base_{0}{1} {{", dt.CompileName, typeParams);
        int ind = indent + IndentAmount;
        Indent(ind);
        wr.WriteLine("public delegate Base_{0}{1} Computer();", dt.CompileName, typeParams);
        Indent(ind);
        wr.WriteLine("public delegate Computer ComputerComputer();");
        Indent(ind);
        wr.WriteLine("Computer c;");
        Indent(ind);
        wr.WriteLine("public {0}__Lazy(Computer c) {{ this.c = c; }}", dt.CompileName);
        Indent(ind);
        wr.WriteLine("public Base_{0}{1} Get() {{ return c(); }}", dt.CompileName, typeParams);
        Indent(indent);
        wr.WriteLine("}");
      }

      int constructorIndex = 0; // used to give each constructor a different
      foreach (DatatypeCtor ctor in dt.Ctors) {
        // class Dt_Ctor<T,U> : Base_Dt<T> {
        //   Fields;
        //   public Dt_Ctor(arguments) {
        //     Fields = arguments;
        //   }
        //   public override bool Equals(object other) {
        //     var oth = other as Dt_Dtor;
        //     return oth != null && equals(_field0, oth._field0) && ... ;
        //   }
        //   public override int GetHashCode() {
        //     return base.GetHashCode();  // surely this can be improved
        //   }
        //   public override string ToString() {  // only for inductive datatypes
        //     // ...
        //   }
        // }
        Indent(indent);
        wr.Write("public class {0}", DtCtorDeclarationName(ctor, dt.TypeArgs));
        wr.WriteLine(" : Base_{0}{1} {{", dt.CompileName, typeParams);
        int ind = indent + IndentAmount;

        int i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind);
            wr.WriteLine("public readonly {0} @{1};", TypeName(arg.Type), FormalName(arg, i));
            i++;
          }
        }

        Indent(ind);
        wr.Write("public {0}(", DtCtorDeclartionName(ctor));
        WriteFormals("", ctor.Formals);
        wr.WriteLine(") {");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            Indent(ind + IndentAmount);
            wr.WriteLine("this.@{0} = @{0};", FormalName(arg, i));
            i++;
          }
        }
        Indent(ind);  wr.WriteLine("}");

        // Equals method
        Indent(ind); wr.WriteLine("public override bool Equals(object other) {");
        Indent(ind + IndentAmount);
        wr.Write("var oth = other as {0}", DtCtorName(ctor, dt.TypeArgs));
        wr.WriteLine(";");
        Indent(ind + IndentAmount);
        wr.Write("return oth != null");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            if (arg.Type.IsDatatype || arg.Type.IsTypeParameter) {
              wr.Write(" && this.@{0}.Equals(oth.@{0})", nm);
            } else {
              wr.Write(" && this.@{0} == oth.@{0}", nm);
            }
            i++;
          }
        }
        wr.WriteLine(";");
        Indent(ind); wr.WriteLine("}");

        // GetHashCode method
        Indent(ind); wr.WriteLine("public override int GetHashCode() {");
        Indent(ind + IndentAmount); wr.Write("return " + constructorIndex);

        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            wr.Write(" ^ this.@{0}.GetHashCode()", nm);
            i++;
          }
        }
        wr.WriteLine(";");
        Indent(ind); wr.WriteLine("}");

        if (dt is IndDatatypeDecl) {
          Indent(ind); wr.WriteLine("public override string ToString() {");
          string nm = (dt.Module.IsDefaultModule ? "" : dt.Module.CompileName + ".") + dt.CompileName + "." + ctor.CompileName;
          Indent(ind + IndentAmount); wr.WriteLine("string s = \"{0}\";", nm);
          if (ctor.Formals.Count != 0) {
            Indent(ind + IndentAmount); wr.WriteLine("s += \"(\";");
            i = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                if (i != 0) {
                  Indent(ind + IndentAmount); wr.WriteLine("s += \", \";");
                }
                Indent(ind + IndentAmount); wr.WriteLine("s += @{0}.ToString();", FormalName(arg, i));
                i++;
              }
            }
            Indent(ind + IndentAmount); wr.WriteLine("s += \")\";");
          }
          Indent(ind + IndentAmount); wr.WriteLine("return s;");
          Indent(ind); wr.WriteLine("}");
        }

        Indent(indent);  wr.WriteLine("}");
      }
      constructorIndex ++;
    }

    void CompileDatatypeStruct(DatatypeDecl dt, int indent) {
      Contract.Requires(dt != null);

      // public struct Dt<T> : IDatatype{
      //   Base_Dt<T> _d;
      //   public Base_Dt<T> _D {
      //     get {
      //       if (_d == null) {
      //         _d = Default;
      //       } else if (_d is Dt__Lazy<T>) {        // co-datatypes only
      //         _d = ((Dt__Lazy<T>)_d).Get();         // co-datatypes only
      //       }
      //       return _d;
      //     }
      //   }
      //   public Dt(Base_Dt<T> d) { this._d = d; }
      //   static Base_Dt<T> theDefault;
      //   public static Base_Dt<T> Default {
      //     get {
      //       if (theDefault == null) {
      //         theDefault = ...;
      //       }
      //       return theDefault;
      //     }
      //   }
      //   public override bool Equals(object other) {
      //     return other is Dt<T> && _D.Equals(((Dt<T>)other)._D);
      //   }
      //   public override int GetHashCode() { return _D.GetHashCode(); }
      //   public override string ToString() { return _D.ToString(); }  // only for inductive datatypes
      //
      //   public bool is_Ctor0 { get { return _D is Dt_Ctor0; } }
      //   ...
      //
      //   public T0 dtor_Dtor0 { get { return ((DT_Ctor)_D).@Dtor0; } }
      //   ...
      // }
      string DtT = dt.CompileName;
      string DtT_TypeArgs = "";
      if (dt.TypeArgs.Count != 0) {
        DtT_TypeArgs = "<" + TypeParameters(dt.TypeArgs) + ">";
        DtT += DtT_TypeArgs;
      }

      Indent(indent);
      wr.WriteLine("public struct @{0} {{", DtT);
      int ind = indent + IndentAmount;

      Indent(ind);
      wr.WriteLine("Base_{0} _d;", DtT);

      Indent(ind);
      wr.WriteLine("public Base_{0} _D {{", DtT);
      Indent(ind + IndentAmount);
      wr.WriteLine("get {");
      Indent(ind + 2 * IndentAmount);
      wr.WriteLine("if (_d == null) {");
      Indent(ind + 3 * IndentAmount);
      wr.WriteLine("_d = Default;");
      if (dt is CoDatatypeDecl) {
        string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
        Indent(ind + 2 * IndentAmount);
        wr.WriteLine("}} else if (_d is {0}__Lazy{1}) {{", dt.CompileName, typeParams);
        Indent(ind + 3 * IndentAmount);
        wr.WriteLine("_d = (({0}__Lazy{1})_d).Get();", dt.CompileName, typeParams);
      }
      Indent(ind + 2 * IndentAmount);  wr.WriteLine("}");
      Indent(ind + 2 * IndentAmount);  wr.WriteLine("return _d;");
      Indent(ind + IndentAmount);  wr.WriteLine("}");
      Indent(ind);  wr.WriteLine("}");

      Indent(ind);
      wr.WriteLine("public @{0}(Base_{1} d) {{ this._d = d; }}", dt.CompileName, DtT);

      Indent(ind);
      wr.WriteLine("static Base_{0} theDefault;", DtT);

      Indent(ind);
      wr.WriteLine("public static Base_{0} Default {{", DtT);
      Indent(ind + IndentAmount);
      wr.WriteLine("get {");
      Indent(ind + 2 * IndentAmount);
      wr.WriteLine("if (theDefault == null) {");
      Indent(ind + 3 * IndentAmount);
      wr.Write("theDefault = ");

      DatatypeCtor defaultCtor;
      if (dt is IndDatatypeDecl) {
        defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
      } else {
        defaultCtor = ((CoDatatypeDecl)dt).Ctors[0];  // pick any one of them
      }
      wr.Write("new {0}", DtCtorName(defaultCtor, dt.TypeArgs));
      wr.Write("(");
      string sep = "";
      foreach (Formal f in defaultCtor.Formals) {
        if (!f.IsGhost) {
          wr.Write("{0}{1}", sep, DefaultValue(f.Type));
          sep = ", ";
        }
      }
      wr.Write(")");
      
      wr.WriteLine(";");
      Indent(ind + 2 * IndentAmount);
      wr.WriteLine("}");
      Indent(ind + 2 * IndentAmount);
      wr.WriteLine("return theDefault;");
      Indent(ind + IndentAmount); wr.WriteLine("}");

      Indent(ind);  wr.WriteLine("}");

      Indent(ind);  wr.WriteLine("public override bool Equals(object other) {");
      Indent(ind + IndentAmount);
      wr.WriteLine("return other is @{0} && _D.Equals(((@{0})other)._D);", DtT);
      Indent(ind);  wr.WriteLine("}");

      Indent(ind);
      wr.WriteLine("public override int GetHashCode() { return _D.GetHashCode(); }");
      if (dt is IndDatatypeDecl) {
        Indent(ind);
        wr.WriteLine("public override string ToString() { return _D.ToString(); }");
      }

      // query properties
      foreach (var ctor in dt.Ctors) {
        //   public bool is_Ctor0 { get { return _D is Dt_Ctor0; } }
        Indent(ind);
        wr.WriteLine("public bool is_{0} {{ get {{ return _D is {1}_{0}{2}; }} }}", ctor.CompileName, dt.CompileName, DtT_TypeArgs);
      }
      if (dt.HasFinitePossibleValues) {
        Indent(ind);
        wr.WriteLine("public static System.Collections.Generic.IEnumerable<@{0}> AllSingletonConstructors {{", DtT);
        Indent(ind + IndentAmount);
        wr.WriteLine("get {");
        foreach (var ctr in dt.Ctors) {
          if (ctr.Formals.Count == 0) {
            Indent(ind + IndentAmount + IndentAmount);
            wr.WriteLine("yield return new @{0}(new {2}_{1}());", DtT, ctr.CompileName, dt.CompileName);
          }
        }
        Indent(ind + IndentAmount + IndentAmount);
        wr.WriteLine("yield break;");
        Indent(ind + IndentAmount);
        wr.WriteLine("}");
        Indent(ind);
        wr.WriteLine("}");
      }
  
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost && arg.HasName) {
            //   public T0 @Dtor0 { get { return ((DT_Ctor)_D).@Dtor0; } }
            Indent(ind);
            wr.WriteLine("public {0} dtor_{1} {{ get {{ return (({2}_{3}{4})_D).@{1}; }} }}", TypeName(arg.Type), arg.CompileName, dt.CompileName, ctor.CompileName, DtT_TypeArgs);
          }
        }
      }

      Indent(indent);
      wr.WriteLine("}");
    }

    int WriteFormals(string sep, List<Formal/*!*/>/*!*/ formals)
    {
      Contract.Requires(sep != null);
      Contract.Requires(cce.NonNullElements(formals));
      int i = 0;
      foreach (Formal arg in formals) {
        if (!arg.IsGhost) {
          string name = FormalName(arg, i);
          wr.Write("{0}{1}{2} @{3}", sep, arg.InParam ? "" : "out ", TypeName(arg.Type), name);
          sep = ", ";
          i++;
        }
      }
      return i;  // the number of formals written
    }

    string FormalName(Formal formal, int i) {
      Contract.Requires(formal != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return formal.HasName ? formal.CompileName : "_a" + i;
    }

    string DtName(DatatypeDecl decl) {
      return decl.Module.IsDefaultModule ? decl.CompileName : decl.FullCompileName;
    }
    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return DtName(ctor.EnclosingDatatype) + "_" + ctor.CompileName;
    }
    string DtCtorDeclartionName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return ctor.EnclosingDatatype.CompileName + "_" + ctor.CompileName;
    }

    string DtCtorName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
    }
    string DtCtorDeclarationName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorDeclartionName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
    }

    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeArgs != null && typeArgs.Count != 0) {
        s += "<" + TypeNames(typeArgs) + ">";
      }
      return s;
    }

    public bool HasMain(Program program) {
      foreach (var module in program.Modules) {
        foreach (var decl in module.TopLevelDecls) {
          var c = decl as ClassDecl;
          if (c != null) {
            foreach (var member in c.Members) {
              var m = member as Method;
              if (m != null) {
                if (!m.IsGhost && m.Name == "Main" && m.Ins.Count == 0 && m.Outs.Count == 0 && m.Req.Count == 0) {
                  return true;
                }
              }
            }
          }
        }
      }
      return false;
    }

    void CompileClassMembers(ClassDecl c, int indent)
    {
      Contract.Requires(c != null);
      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          Field f = (Field)member;
          if (!f.IsGhost) {
            Indent(indent);
            wr.WriteLine("public {0} @{1} = {2};", TypeName(f.Type), f.CompileName, DefaultValue(f.Type));
          }

        } else if (member is Function) {
          Function f = (Function)member;
          if (f.Body == null) {
            if (!Attributes.Contains(f.Attributes, "axiom")) {
              Error("Function {0} has no body", f.FullName);
            }
          } else if (f.IsGhost) {
            var v = new CheckHasNoAssumes_Visitor(this);
            v.Visit(f.Body);
          } else {
            Indent(indent);
            wr.Write("public {0}{1} @{2}", f.IsStatic ? "static " : "", TypeName(f.ResultType), f.CompileName);
            if (f.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(f.TypeArgs));
            }
            wr.Write("(");
            WriteFormals("", f.Formals);
            wr.WriteLine(") {");
            CompileReturnBody(f.Body, indent + IndentAmount);
            Indent(indent); wr.WriteLine("}");
          }

        } else if (member is Method) {
          Method m = (Method)member;
          if (m.Body == null) {
            if (!Attributes.Contains(m.Attributes, "axiom")) {
              Error("Method {0} has no body", m.FullName);
            }
          } else if (m.IsGhost) {
            var v = new CheckHasNoAssumes_Visitor(this);
            v.Visit(m.Body);
          } else {
            Indent(indent);
            wr.Write("public {0}void @{1}", m.IsStatic ? "static " : "", m.CompileName);
            if (m.TypeArgs.Count != 0) {
              wr.Write("<{0}>", TypeParameters(m.TypeArgs));
            }
            wr.Write("(");
            int nIns = WriteFormals("", m.Ins);
            WriteFormals(nIns == 0 ? "" : ", ", m.Outs);
            wr.WriteLine(")");
            Indent(indent);  wr.WriteLine("{");
            foreach (Formal p in m.Outs) {
              if (!p.IsGhost) {
                Indent(indent + IndentAmount);
                wr.WriteLine("@{0} = {1};", p.CompileName, DefaultValue(p.Type));
              }
            }
            if (m.Body == null) {
              Error("Method {0} has no body", m.FullName);
            } else {
              if (m.IsTailRecursive) {
                Indent(indent); wr.WriteLine("TAIL_CALL_START: ;");
                if (!m.IsStatic) {
                  Indent(indent + IndentAmount); wr.WriteLine("var _this = this;");
                }
              }
              Contract.Assert(enclosingMethod == null);
              enclosingMethod = m;
              TrStmtList(m.Body.Body, indent);
              Contract.Assert(enclosingMethod == m);
              enclosingMethod = null;
            }
            Indent(indent);  wr.WriteLine("}");

            // allow the Main method to be an instance method
            if (!m.IsStatic && m.Name == "Main" && m.Ins.Count == 0 && m.Outs.Count == 0 && m.Req.Count == 0) {
              Indent(indent);
              wr.WriteLine("public static void Main(string[] args) {");
              Contract.Assert(m.EnclosingClass == c);
              Indent(indent + IndentAmount);
              wr.Write("@{0} b = new @{0}", c.CompileName);
              if (c.TypeArgs.Count != 0) {
                // instantiate every parameter, it doesn't particularly matter how
                wr.Write("<");
                string sep = "";
                for (int i = 0; i < c.TypeArgs.Count; i++) {
                  wr.Write("{0}int", sep);
                  sep = ", ";
                }
                wr.Write(">");
              }
              wr.WriteLine("();");
              Indent(indent + IndentAmount);  wr.WriteLine("b.@Main();");
              Indent(indent);  wr.WriteLine("}");
            }
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    void CompileReturnBody(Expression body, int indent) {
      Contract.Requires(0 <= indent);
      body = body.Resolved;
      SpillLetVariableDecls(body, indent);
      Indent(indent);
      wr.Write("return ");
      TrExpr(body);
      wr.WriteLine(";");
    }

    void SpillLetVariableDecls(Expression expr, int indent) {
      Contract.Requires(0 <= indent);
      if (expr == null) {
        // allow "null" as an argument; nothing to do
        return;
      }
      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        // Bound variables introduced in the LHS are ghost if either the entire let expression is declared
        // a ghost or the position of a variable corresponds to the datatype constructor argument that is
        // declared a ghost.  If all variables are ghost, then the corresponding RHS is not needed; but if
        // there is any non-ghost variable, then the corresponding RHS is needed.
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);
        var i = 0;
        foreach (var lhs in e.LHSs) {
          var needRHS = false;
          foreach (var v in lhs.Vars) {
            if (!v.IsGhost) {
              if (!needRHS) {
                // this is the first of lhs's variables that we have found we need
                Indent(indent);
                var nm = string.Format("_pat_let{0}_{1}", GetUniqueAstNumber(e), i);
                wr.WriteLine("{0} @{1};", TypeName(e.RHSs[i].Type), nm);
                needRHS = true;
              }
              Indent(indent);
              wr.WriteLine("{0} @{1};", TypeName(v.Type), v.CompileName);
            }
          }
          if (needRHS) {
            SpillLetVariableDecls(e.RHSs[i], indent);
          }
          i++;
        }
        SpillLetVariableDecls(e.Body, indent);
        return;
      }
      foreach (var ee in expr.SubExpressions) {
        SpillLetVariableDecls(ee, indent);
      }
    }

    // ----- Type ---------------------------------------------------------------------------------

    readonly string DafnySetClass = "Dafny.Set";
    readonly string DafnyMultiSetClass = "Dafny.MultiSet";
    readonly string DafnySeqClass = "Dafny.Sequence";
    readonly string DafnyMapClass = "Dafny.Map";

    string TypeName(Type type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return "object";
        } else {
          type = tp.T;
        }
      }

      if (type is BoolType) {
        return "bool";
      } else if (type is IntType) {
        return "BigInteger";
      } else if (type is RealType) {
        return "Dafny.BigRational";
      } else if (type is ObjectType) {
        return "object";
      } else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(type);
        string name = TypeName(elType) + "[";
        for (int i = 1; i < at.Dims; i++) {
          name += ",";
        }
        return name + "]";
      } else if (type is UserDefinedType) {
        UserDefinedType udt = (UserDefinedType)type;
        string s = "@" + udt.FullCompileName;
        if (udt.TypeArgs.Count != 0) {
          if (udt.TypeArgs.Exists(argType => argType is ObjectType)) {
            Error("compilation does not support type 'object' as a type parameter; consider introducing a ghost");
          }
          s += "<" + TypeNames(udt.TypeArgs) + ">";
        }
        return s;
      } else if (type is SetType) {
        Type argType = ((SetType)type).Arg;
        if (argType is ObjectType) {
          Error("compilation of set<object> is not supported; consider introducing a ghost");
        }
        return DafnySetClass + "<" + TypeName(argType) + ">";
      } else if (type is SeqType) {
        Type argType = ((SeqType)type).Arg;
        if (argType is ObjectType) {
          Error("compilation of seq<object> is not supported; consider introducing a ghost");
        }
        return DafnySeqClass + "<" + TypeName(argType) + ">";
      } else if (type is MultiSetType) {
        Type argType = ((MultiSetType)type).Arg;
        if (argType is ObjectType) {
          Error("compilation of seq<object> is not supported; consider introducing a ghost");
        }
        return DafnyMultiSetClass + "<" + TypeName(argType) + ">";
      } else if (type is MapType) {
        Type domType = ((MapType)type).Domain;
        Type ranType = ((MapType)type).Range;
        if (domType is ObjectType || ranType is ObjectType) {
          Error("compilation of map<object, _> or map<_, object> is not supported; consider introducing a ghost");
        }
        return DafnyMapClass + "<" + TypeName(domType) + "," + TypeName(ranType) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    string/*!*/ TypeNames(List<Type/*!*/>/*!*/ types) {
      Contract.Requires(cce.NonNullElements(types));
      Contract.Ensures(Contract.Result<string>() != null);

      string s = "";
      string sep = "";
      foreach (Type t in types) {
        s += sep + TypeName(t);
        sep = ",";
      }
      return s;
    }

    string/*!*/ TypeParameters(List<TypeParameter/*!*/>/*!*/ targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      string s = "";
      string sep = "";
      foreach (TypeParameter tp in targs) {
        s += sep + "@" + tp.CompileName;
        sep = ",";
      }
      return s;
    }

    string DefaultValue(Type type)
    {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<string>() != null);

      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return "null";
        } else {
          type = tp.T;
        }
      }

      if (type is BoolType) {
        return "false";
      } else if (type is IntType) {
        return "new BigInteger(0)";
      } else if (type is RealType) {
        return "Dafny.BigRational.ZERO";
      } else if (type.IsRefType) {
        return string.Format("({0})null", TypeName(type));
      } else if (type.IsDatatype) {
        UserDefinedType udt = (UserDefinedType)type;
        string s = "@" + udt.FullCompileName;
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs) + ">";
        }
        return string.Format("new {0}()", s);
      } else if (type.IsTypeParameter) {
        UserDefinedType udt = (UserDefinedType)type;
        return "default(@" + udt.FullCompileName + ")";
      } else if (type is SetType) {
        return DafnySetClass + "<" + TypeName(((SetType)type).Arg) + ">.Empty";
      } else if (type is MultiSetType) {
        return DafnyMultiSetClass + "<" + TypeName(((MultiSetType)type).Arg) + ">.Empty";
      } else if (type is SeqType) {
        return DafnySeqClass + "<" + TypeName(((SeqType)type).Arg) + ">.Empty";
      } else if (type is MapType) {
        return TypeName(type)+".Empty";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    // ----- Stmt ---------------------------------------------------------------------------------

    public class CheckHasNoAssumes_Visitor : BottomUpVisitor
    {
      readonly Compiler compiler;
      public CheckHasNoAssumes_Visitor(Compiler c) {
        Contract.Requires(c != null);
        compiler = c;
      }
      protected override void VisitOneStmt(Statement stmt) {
        if (stmt is AssumeStmt) {
          compiler.Error("an assume statement cannot be compiled (line {0})", stmt.Tok.line);
        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          if (s.AssumeToken != null) {
            compiler.Error("an assume statement cannot be compiled (line {0})", s.AssumeToken.line);
          }
        }
      }
    }

    void TrStmt(Statement stmt, int indent)
    {
      Contract.Requires(stmt != null);
      if (stmt.IsGhost) {
        var v = new CheckHasNoAssumes_Visitor(this);
        v.Visit(stmt);
        Indent(indent); wr.WriteLine("{ }");
        return;
      }

      if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        foreach (Attributes.Argument arg in s.Args) {
          SpillLetVariableDecls(arg.E, indent);
          Indent(indent);
          wr.Write("System.Console.Write(");
          if (arg.S != null) {
            wr.Write("\"{0}\"", arg.S);
          } else {
            Contract.Assert(arg.E != null);
            TrExpr(arg.E);
          }
          wr.WriteLine(");");
        }
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        Indent(indent);
        wr.WriteLine("goto after_{0};", s.TargetStmt.Labels.Data.UniqueId);
      } else if (stmt is ProduceStmt) {
        var s = (ProduceStmt)stmt;
        if (s.hiddenUpdate != null)
          TrStmt(s.hiddenUpdate, indent);
        Indent(indent);
        if (s is YieldStmt) {
          wr.WriteLine("yield return null;");
        } else {
          wr.WriteLine("return;");
        }
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        var resolved = s.ResolvedStatements;
        if (resolved.Count == 1) {
          TrStmt(resolved[0], indent);
        } else {
          // multi-assignment
          Contract.Assert(s.Lhss.Count == resolved.Count);
          Contract.Assert(s.Rhss.Count == resolved.Count);
          var lvalues = new List<string>();
          var rhss = new List<string>();
          for (int i = 0; i < resolved.Count; i++) {
            if (!resolved[i].IsGhost) {
              var lhs = s.Lhss[i];
              var rhs = s.Rhss[i];
              if (!(rhs is HavocRhs)) {
                lvalues.Add(CreateLvalue(lhs, indent));

                string target = "_rhs" + tmpVarCount;
                tmpVarCount++;
                rhss.Add(target);
                TrRhs("var " + target, null, rhs, indent);
              }
            }
          }
          Contract.Assert(lvalues.Count == rhss.Count);
          for (int i = 0; i < lvalues.Count; i++) {
            Indent(indent);
            wr.WriteLine("{0} = {1};", lvalues[i], rhss[i]);
          }
        }

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        Contract.Assert(!(s.Lhs is SeqSelectExpr) || ((SeqSelectExpr)s.Lhs).SelectOne);  // multi-element array assignments are not allowed
        TrRhs(null, s.Lhs, s.Rhs, indent);

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        if (s.AssumeToken != null) {
          // Note, a non-ghost AssignSuchThatStmt may contain an assume
          Error("an assume statement cannot be compiled (line {0})", s.AssumeToken.line);
        } else  if (s.MissingBounds != null) {
          foreach (var bv in s.MissingBounds) {
            Error("this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}' (line {1})", bv.Name, s.Tok.line);
          }
        } else {
          Contract.Assume(s.Bounds != null);
          SpillLetVariableDecls(s.Expr, indent);

          // For "i,j,k,l :| R(i,j,k,l);", emit something like:
          //
          // for (BigInteger iterLimit = 5; ; iterLimit *= 2) {
          //   var il$0 = iterLimit;
          //   foreach (L l' in sq.Elements) { l = l';
          //     if (il$0 == 0) { break; }  il$0--;
          //     var il$1 = iterLimit;
          //     foreach (K k' in st.Elements) { k = k';
          //       if (il$1 == 0) { break; }  il$1--;
          //       var il$2 = iterLimit;
          //       j = Lo;
          //       for (;; j++) {
          //         if (il$2 == 0) { break; }  il$2--;
          //         foreach (bool i' in Helper.AllBooleans) { i = i';
          //           if (R(i,j,k,l)) {
          //             goto ASSIGN_SUCH_THAT_<id>;
          //           }
          //         }
          //       }
          //     }
          //   }
          // }
          // throw new Exception("assign-such-that search produced no value"); // a verified program never gets here; however, we need this "throw" to please the C# compiler
          // ASSIGN_SUCH_THAT_<id>: ;
          //
          // where the iterLimit loop can be omitted if s.Lhss.Count == 1 or if all bounds are finite.  Further optimizations could be done, but
          // are omitted for now.
          //
          Contract.Assert(s.Bounds != null);  // follows from s.MissingBounds == null
          var n = s.Lhss.Count;
          Contract.Assert(s.Bounds.Count == n);
          var doneLabel = "_ASSIGN_SUCH_THAT_" + tmpVarCount;
          var iterLimit = "_iterLimit_" + tmpVarCount;
          tmpVarCount++;

          int ind = indent;
          bool needIterLimit = s.Lhss.Count != 1 && s.Bounds.Exists(bnd => !bnd.IsFinite);
          if (needIterLimit) {
            Indent(indent);
            wr.WriteLine("for (var {0} = new BigInteger(5); ; {0} *= 2) {{", iterLimit);
            ind += IndentAmount;
          }

          for (int i = 0; i < n; i++, ind += IndentAmount) {
            var bound = s.Bounds[i];
            var bv = ((IdentifierExpr)s.Lhss[i].Resolved).Var;  // the resolver allows only IdentifierExpr left-hand sides
            if (needIterLimit) {
              Indent(ind);
              wr.WriteLine("var {0}_{1} = {0};", iterLimit, i);
            }
            var tmpVar = "_assign_such_that_" + tmpVarCount;
            tmpVarCount++;
            Indent(ind);
            if (bound is ComprehensionExpr.BoolBoundedPool) {
              wr.WriteLine("foreach (var {0} in Dafny.Helpers.AllBooleans) {{ @{1} = {0};", tmpVar, bv.CompileName);
            } else if (bound is ComprehensionExpr.IntBoundedPool) {
              var b = (ComprehensionExpr.IntBoundedPool)bound;
              // (tmpVar is not used in this case)
              if (b.LowerBound != null) {
                wr.Write("@{0} = ", bv.CompileName);
                TrExpr(b.LowerBound);
                wr.WriteLine(";");
                Indent(ind);
                if (b.UpperBound != null) {
                  wr.Write("for (; @{0} < ", bv.CompileName);
                  TrExpr(b.UpperBound);
                  wr.WriteLine("; @{0}++) {{ ", bv.CompileName);
                } else {
                  wr.WriteLine("for (;; @{0}++) {{ ", bv.CompileName);
                }
              } else {
                Contract.Assert(b.UpperBound != null);
                wr.Write("@{0} = ", bv.CompileName);
                TrExpr(b.UpperBound);
                wr.WriteLine(";");
                Indent(ind);
                wr.WriteLine("for (;; @{0}--) {{ ", bv.CompileName);
              }
            } else if (bound is AssignSuchThatStmt.WiggleWaggleBound) {
              wr.WriteLine("foreach (var {0} in Dafny.Helpers.AllIntegers) {{ @{1} = {0};", tmpVar, bv.CompileName);
            } else if (bound is ComprehensionExpr.SetBoundedPool) {
              var b = (ComprehensionExpr.SetBoundedPool)bound;
              wr.Write("foreach (var {0} in (", tmpVar);
              TrExpr(b.Set);
              wr.WriteLine(").Elements) {{ @{0} = {1};", bv.CompileName, tmpVar);
            } else if (bound is ComprehensionExpr.SubSetBoundedPool) {
              var b = (ComprehensionExpr.SubSetBoundedPool)bound;
              wr.Write("foreach (var {0} in (", tmpVar);
              TrExpr(b.UpperBound);
              wr.WriteLine(").AllSubsets) {{ @{0} = {1};", bv.CompileName, tmpVar);
            } else if (bound is ComprehensionExpr.MapBoundedPool) {
              var b = (ComprehensionExpr.MapBoundedPool)bound;
              wr.Write("foreach (var {0} in (", tmpVar);
              TrExpr(b.Map);
              wr.WriteLine(").Domain) {{ @{0} = {1};", bv.CompileName, tmpVar);
            } else if (bound is ComprehensionExpr.SeqBoundedPool) {
              var b = (ComprehensionExpr.SeqBoundedPool)bound;
              wr.Write("foreach (var {0} in (", tmpVar);
              TrExpr(b.Seq);
              wr.WriteLine(").Elements) {{ @{0} = {1};", bv.CompileName, tmpVar);
            } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
              var b = (ComprehensionExpr.DatatypeBoundedPool)bound;
              wr.WriteLine("foreach (var {0} in {1}.AllSingletonConstructors) {{ @{2} = {0};", tmpVar, TypeName(bv.Type), bv.CompileName);
            } else {
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
            }
            if (needIterLimit) {
              Indent(ind + IndentAmount);
              wr.WriteLine("if ({0}_{1} == 0) {{ break; }}  {0}_{1}--;", iterLimit, i);
            }
          }
          Indent(ind);
          wr.Write("if (");
          TrExpr(s.Expr);
          wr.WriteLine(") {");
          Indent(ind + IndentAmount);
          wr.WriteLine("goto {0};", doneLabel);
          Indent(ind);
          wr.WriteLine("}");
          Indent(indent);
          for (int i = 0; i < n; i++) {
            wr.Write(i == 0 ? "}" : " }");
          }
          wr.WriteLine(needIterLimit ? " }" : "");
          Indent(indent);
          wr.WriteLine("throw new System.Exception(\"assign-such-that search produced no value (line {0})\");", s.Tok.line);
          Indent(indent);
          wr.WriteLine("{0}: ;", doneLabel);
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        TrCallStmt(s, null, indent);

      } else if (stmt is BlockStmt) {
        Indent(indent);  wr.WriteLine("{");
        TrStmtList(((BlockStmt)stmt).Body, indent);
        Indent(indent);  wr.WriteLine("}");

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard == null) {
          // we can compile the branch of our choice
          if (s.Els == null) {
            // let's compile the "else" branch, since that involves no work
            // (still, let's leave a marker in the source code to indicate that this is what we did)
            Indent(indent);
            wr.WriteLine("if (!false) { }");
          } else {
            // let's compile the "then" branch
            Indent(indent);
            wr.WriteLine("if (true)");
            TrStmt(s.Thn, indent);
          }
        } else {
          SpillLetVariableDecls(s.Guard, indent);
          Indent(indent);  wr.Write("if (");
          TrExpr(s.Guard);
          wr.WriteLine(")");

          TrStmt(s.Thn, indent);
          if (s.Els != null) {
            Indent(indent);  wr.WriteLine("else");
            TrStmt(s.Els, indent);
          }
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        foreach (var alternative in s.Alternatives) {
          SpillLetVariableDecls(alternative.Guard, indent);
        }
        Indent(indent);
        foreach (var alternative in s.Alternatives) {
          wr.Write("if (");
          TrExpr(alternative.Guard);
          wr.WriteLine(") {");
          TrStmtList(alternative.Body, indent);
          Indent(indent);
          wr.Write("} else ");
        }
        wr.WriteLine("{ /*unreachable alternative*/ }");

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        if (s.Guard == null) {
          Indent(indent);
          wr.WriteLine("while (false) { }");
        } else {
          SpillLetVariableDecls(s.Guard, indent);
          Indent(indent);
          wr.Write("while (");
          TrExpr(s.Guard);
          wr.WriteLine(")");
          TrStmt(s.Body, indent);
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        if (s.Alternatives.Count != 0) {
          Indent(indent);
          wr.WriteLine("while (true) {");
          int ind = indent + IndentAmount;
          foreach (var alternative in s.Alternatives) {
            SpillLetVariableDecls(alternative.Guard, ind);
          }
          Indent(ind);
          foreach (var alternative in s.Alternatives) {
            wr.Write("if (");
            TrExpr(alternative.Guard);
            wr.WriteLine(") {");
            TrStmtList(alternative.Body, ind);
            Indent(ind);
            wr.Write("} else ");
          }
          wr.WriteLine("{ break; }");
          Indent(indent);
          wr.WriteLine("}");
        }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        if (s.Kind != ForallStmt.ParBodyKind.Assign) {
          // Call and Proof have no side effects, so they can simply be optimized away.
          return;
        } else if (s.BoundVars.Count == 0) {
          // the bound variables just spell out a single point, so the forall statement is equivalent to one execution of the body
          TrStmt(s.Body, indent);
          return;
        }
        var s0 = (AssignStmt)s.S0;
        if (s0.Rhs is HavocRhs) {
          // The forall statement says to havoc a bunch of things.  This can be efficiently compiled
          // into doing nothing.
          return;
        }
        var rhs = ((ExprRhs)s0.Rhs).Expr;

        // Compile:
        //   forall (w,x,y,z | Range(w,x,y,z)) {
        //     LHS(w,x,y,z) := RHS(w,x,y,z);
        //   }
        // where w,x,y,z have types seq<W>,set<X>,int,bool and LHS has L-1 top-level subexpressions
        // (that is, L denotes the number of top-level subexpressions of LHS plus 1),
        // into:
        //   var ingredients = new List< L-Tuple >();
        //   foreach (W w in sq.UniqueElements) {
        //     foreach (X x in st.Elements) {
        //       for (BigInteger y = Lo; j < Hi; j++) {
        //         for (bool z in Helper.AllBooleans) {
        //           if (Range(w,x,y,z)) {
        //             ingredients.Add(new L-Tuple( LHS0(w,x,y,z), LHS1(w,x,y,z), ..., RHS(w,x,y,z) ));
        //           }
        //         }
        //       }
        //     }
        //   }
        //   foreach (L-Tuple l in ingredients) {
        //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
        //   }
        //
        // Note, because the .NET Tuple class only supports up to 8 components, the compiler implementation
        // here supports arrays only up to 6 dimensions.  This does not seem like a serious practical limitation.
        // However, it may be more noticeable if the forall statement supported forall assignments in its
        // body.  To support cases where tuples would need more than 8 components, .NET Tuple's would have to
        // be nested.

        // Temporary names
        string ingredients = "_ingredients" + tmpVarCount;
        string tup = "_tup" + tmpVarCount;
        tmpVarCount++;

        // Compute L
        int L;
        string tupleTypeArgs;
        if (s0.Lhs is FieldSelectExpr) {
          var lhs = (FieldSelectExpr)s0.Lhs;
          L = 2;
          tupleTypeArgs = TypeName(lhs.Obj.Type);
        } else if (s0.Lhs is SeqSelectExpr) {
          var lhs = (SeqSelectExpr)s0.Lhs;
          L = 3;
          // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
          tupleTypeArgs = TypeName(lhs.Seq.Type) + ",int";
        } else {
          var lhs = (MultiSelectExpr)s0.Lhs;
          L = 2 + lhs.Indices.Count;
          if (8 < L) {
            Error("compiler currently does not support assignments to more-than-6-dimensional arrays in forall statements");
            return;
          }
          tupleTypeArgs = TypeName(lhs.Array.Type);
          for (int i = 0; i < lhs.Indices.Count; i++) {
            // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
            tupleTypeArgs += ",int";
          }
        }
        tupleTypeArgs += "," + TypeName(rhs.Type);

        // declare and construct "ingredients"
        Indent(indent);
        wr.WriteLine("var {0} = new System.Collections.Generic.List<System.Tuple<{1}>>();", ingredients, tupleTypeArgs);

        var n = s.BoundVars.Count;
        Contract.Assert(s.Bounds.Count == n);
        for (int i = 0; i < n; i++) {
          var ind = indent + i * IndentAmount;
          var bound = s.Bounds[i];
          var bv = s.BoundVars[i];
          if (bound is ComprehensionExpr.BoolBoundedPool) {
            Indent(ind);
            wr.Write("foreach (var @{0} in Dafny.Helpers.AllBooleans) {{ ", bv.CompileName);
          } else if (bound is ComprehensionExpr.IntBoundedPool) {
            var b = (ComprehensionExpr.IntBoundedPool)bound;
            SpillLetVariableDecls(b.LowerBound, ind);
            SpillLetVariableDecls(b.UpperBound, ind);
            Indent(ind);
            wr.Write("for (var @{0} = ", bv.CompileName);
            TrExpr(b.LowerBound);
            wr.Write("; @{0} < ", bv.CompileName);
            TrExpr(b.UpperBound);
            wr.Write("; @{0}++) {{ ", bv.CompileName);
          } else if (bound is ComprehensionExpr.SetBoundedPool) {
            var b = (ComprehensionExpr.SetBoundedPool)bound;
            SpillLetVariableDecls(b.Set, ind);
            Indent(ind);
            wr.Write("foreach (var @{0} in (", bv.CompileName);
            TrExpr(b.Set);
            wr.Write(").Elements) { ");
          } else if (bound is ComprehensionExpr.SeqBoundedPool) {
            var b = (ComprehensionExpr.SeqBoundedPool)bound;
            SpillLetVariableDecls(b.Seq, ind);
            Indent(ind);
            wr.Write("foreach (var @{0} in (", bv.CompileName);
            TrExpr(b.Seq);
            wr.Write(").UniqueElements) { ");
          } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
            var b = (ComprehensionExpr.DatatypeBoundedPool)bound;
            wr.Write("foreach (var @{0} in {1}.AllSingletonConstructors) {{", bv.CompileName, TypeName(bv.Type));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
          }
          wr.WriteLine();
        }

        // if (range) {
        //   ingredients.Add(new L-Tuple( LHS0(w,x,y,z), LHS1(w,x,y,z), ..., RHS(w,x,y,z) ));
        // }
        SpillLetVariableDecls(s.Range, indent + n * IndentAmount);
        Indent(indent + n * IndentAmount);
        wr.Write("if ");
        TrParenExpr(s.Range);
        wr.WriteLine(" {");

        var indFinal = indent + (n + 1) * IndentAmount;
        SpillLetVariableDecls(s0.Lhs, indFinal);
        SpillLetVariableDecls(rhs, indFinal);
        Indent(indFinal);
        wr.Write("{0}.Add(new System.Tuple<{1}>(", ingredients, tupleTypeArgs);
        if (s0.Lhs is FieldSelectExpr) {
          var lhs = (FieldSelectExpr)s0.Lhs;
          TrExpr(lhs.Obj);
        } else if (s0.Lhs is SeqSelectExpr) {
          var lhs = (SeqSelectExpr)s0.Lhs;
          TrExpr(lhs.Seq);
          wr.Write(", (int)(");
          TrExpr(lhs.E0);
          wr.Write(")");
        } else {
          var lhs = (MultiSelectExpr)s0.Lhs;
          TrExpr(lhs.Array);
          for (int i = 0; i < lhs.Indices.Count; i++) {
            wr.Write(", (int)(");
            TrExpr(lhs.Indices[i]);
            wr.Write(")");
          }
          wr.WriteLine("] = {0}.Item{1};", tup, L);
        }
        wr.Write(", ");
        TrExpr(rhs);
        wr.WriteLine("));");

        Indent(indent + n * IndentAmount);
        wr.WriteLine("}");

        for (int i = n; 0 <= --i; ) {
          Indent(indent + i * IndentAmount);
          wr.WriteLine("}");
        }

        //   foreach (L-Tuple l in ingredients) {
        //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
        //   }
        Indent(indent);
        wr.WriteLine("foreach (var {0} in {1}) {{", tup, ingredients);
        Indent(indent + IndentAmount);
        if (s0.Lhs is FieldSelectExpr) {
          var lhs = (FieldSelectExpr)s0.Lhs;
          wr.WriteLine("{0}.Item1.@{1} = {0}.Item2;", tup, lhs.FieldName);
        } else if (s0.Lhs is SeqSelectExpr) {
          var lhs = (SeqSelectExpr)s0.Lhs;
          wr.WriteLine("{0}.Item1[{0}.Item2] = {0}.Item3;", tup);
        } else {
          var lhs = (MultiSelectExpr)s0.Lhs;
          wr.Write("{0}.Item1[");
          string sep = "";
          for (int i = 0; i < lhs.Indices.Count; i++) {
            wr.Write("{0}{1}.Item{2}", sep, tup, i + 2);
            sep = ", ";
          }
          wr.WriteLine("] = {0}.Item{1};", tup, L);
        }
        Indent(indent);
        wr.WriteLine("}");

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        // Type source = e;
        // if (source.is_Ctor0) {
        //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
        //   ...
        //   Body0;
        // } else if (...) {
        //   ...
        // } else if (true) {
        //   ...
        // }
        if (s.Cases.Count != 0) {
          var sourceType = (UserDefinedType)s.Source.Type;

          SpillLetVariableDecls(s.Source, indent);
          string source = "_source" + tmpVarCount;
          tmpVarCount++;
          Indent(indent);
          wr.Write("{0} {1} = ", TypeName(cce.NonNull(s.Source.Type)), source);
          TrExpr(s.Source);
          wr.WriteLine(";");

          int i = 0;
          foreach (MatchCaseStmt mc in s.Cases) {
            MatchCasePrelude(source, sourceType, cce.NonNull(mc.Ctor), mc.Arguments, i, s.Cases.Count, indent);
            TrStmtList(mc.Body, indent);
            i++;
          }
          Indent(indent); wr.WriteLine("}");
        }

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          TrLocalVar(local, true, indent);
        }
        if (s.Update != null) {
          TrStmt(s.Update, indent);
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        if (s.Body != null) {
          TrStmt(s.Body, indent);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    string CreateLvalue(Expression lhs, int indent) {
      lhs = lhs.Resolved;
      SpillLetVariableDecls(lhs, indent);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        return "@" + ll.Var.CompileName;
      } else if (lhs is FieldSelectExpr) {
        var ll = (FieldSelectExpr)lhs;
        string obj = "_obj" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", obj);
        TrExpr(ll.Obj);
        wr.WriteLine(";");
        return string.Format("{0}.@{1}", obj, ll.Field.CompileName);
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        string arr = "_arr" + tmpVarCount;
        string index = "_index" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", arr);
        TrExpr(ll.Seq);
        wr.WriteLine(";");
        Indent(indent);
        wr.Write("var {0} = ", index);
        TrExpr(ll.E0);
        wr.WriteLine(";");
        return string.Format("{0}[(int){1}]", arr, index);
      } else {
        var ll = (MultiSelectExpr)lhs;
        string arr = "_arr" + tmpVarCount;
        Indent(indent);
        wr.Write("var {0} = ", arr);
        TrExpr(ll.Array);
        wr.WriteLine(";");
        string fullString = arr + "[";
        string sep = "";
        int i = 0;
        foreach (var idx in ll.Indices) {
          string index = "_index" + i + "_" + tmpVarCount;
          Indent(indent);
          wr.Write("var {0} = ", index);
          TrExpr(idx);
          wr.WriteLine(";");
          fullString += sep + "(int)" + index;
          sep = ", ";
          i++;
        }
        tmpVarCount++;
        return fullString + "]";
      }
    }

    void TrRhs(string target, Expression targetExpr, AssignmentRhs rhs, int indent) {
      Contract.Requires((target == null) != (targetExpr == null));
      SpillLetVariableDecls(targetExpr, indent);
      var tRhs = rhs as TypeRhs;
      if (tRhs != null && tRhs.InitCall != null) {
        string nw = "_nw" + tmpVarCount;
        tmpVarCount++;
        Indent(indent);
        wr.Write("var {0} = ", nw);
        TrAssignmentRhs(rhs);  // in this case, this call will not require us to spill any let variables first
        wr.WriteLine(";");
        TrCallStmt(tRhs.InitCall, nw, indent);
        Indent(indent);
        if (target != null) {
          wr.Write(target);
        } else {
          TrExpr(targetExpr);
        }
        wr.WriteLine(" = {0};", nw);
      } else if (rhs is HavocRhs) {
        // do nothing
      } else {
        if (rhs is ExprRhs) {
          SpillLetVariableDecls(((ExprRhs)rhs).Expr, indent);
        } else if (tRhs != null && tRhs.ArrayDimensions != null) {
          foreach (Expression dim in tRhs.ArrayDimensions) {
            SpillLetVariableDecls(dim, indent);
          }
        }
        Indent(indent);
        if (target != null) {
          wr.Write(target);
        } else {
          TrExpr(targetExpr);
        }
        wr.Write(" = ");
        TrAssignmentRhs(rhs);
        wr.WriteLine(";");
      }
    }

    void TrCallStmt(CallStmt s, string receiverReplacement, int indent) {
      Contract.Requires(s != null);
      Contract.Assert(s.Method != null);  // follows from the fact that stmt has been successfully resolved

      if (s.Method == enclosingMethod && enclosingMethod.IsTailRecursive) {
        // compile call as tail-recursive

        // assign the actual in-parameters to temporary variables
        var inTmps = new List<string>();
        for (int i = 0; i < s.Method.Ins.Count; i++) {
          Formal p = s.Method.Ins[i];
          if (!p.IsGhost) {
            SpillLetVariableDecls(s.Args[i], indent);
          }
        }
        if (receiverReplacement != null) {
          // TODO:  What to do here?  When does this happen, what does it mean?
        } else if (!s.Method.IsStatic) {
          SpillLetVariableDecls(s.Receiver, indent);

          string inTmp = "_in" + tmpVarCount;
          tmpVarCount++;
          inTmps.Add(inTmp);
          Indent(indent);
          wr.Write("var {0} = ", inTmp);
          TrExpr(s.Receiver);
          wr.WriteLine(";");
        }
        for (int i = 0; i < s.Method.Ins.Count; i++) {
          Formal p = s.Method.Ins[i];
          if (!p.IsGhost) {
            string inTmp = "_in" + tmpVarCount;
            tmpVarCount++;
            inTmps.Add(inTmp);
            Indent(indent);
            wr.Write("var {0} = ", inTmp);
            TrExpr(s.Args[i]);
            wr.WriteLine(";");
          }
        }
        // Now, assign to the formals
        int n = 0;
        if (!s.Method.IsStatic) {
          Indent(indent);
          wr.WriteLine("_this = {0};", inTmps[n]);
          n++;
        }
        foreach (var p in s.Method.Ins) {
          if (!p.IsGhost) {
            Indent(indent);
            wr.WriteLine("{0} = {1};", p.CompileName, inTmps[n]);
            n++;
          }
        }
        Contract.Assert(n == inTmps.Count);
        // finally, the jump back to the head of the method
        Indent(indent);
        wr.WriteLine("goto TAIL_CALL_START;");

      } else {
        // compile call as a regular call

        var lvalues = new List<string>();
        Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);
        for (int i = 0; i < s.Method.Outs.Count; i++) {
          Formal p = s.Method.Outs[i];
          if (!p.IsGhost) {
            lvalues.Add(CreateLvalue(s.Lhs[i], indent));
          }
        }
        var outTmps = new List<string>();
        for (int i = 0; i < s.Method.Outs.Count; i++) {
          Formal p = s.Method.Outs[i];
          if (!p.IsGhost) {
            string target = "_out" + tmpVarCount;
            tmpVarCount++;
            outTmps.Add(target);
            Indent(indent);
            wr.WriteLine("{0} {1};", TypeName(s.Lhs[i].Type), target);
          }
        }
        Contract.Assert(lvalues.Count == outTmps.Count);

        for (int i = 0; i < s.Method.Ins.Count; i++) {
          Formal p = s.Method.Ins[i];
          if (!p.IsGhost) {
            SpillLetVariableDecls(s.Args[i], indent);
          }
        }
        if (receiverReplacement != null) {
          Indent(indent);
          wr.Write("@" + receiverReplacement);
        } else if (s.Method.IsStatic) {
          Indent(indent);
          wr.Write(TypeName(cce.NonNull(s.Receiver.Type)));
        } else {
          SpillLetVariableDecls(s.Receiver, indent);
          Indent(indent);
          TrParenExpr(s.Receiver);
        }
        wr.Write(".@{0}(", s.Method.CompileName);

        string sep = "";
        for (int i = 0; i < s.Method.Ins.Count; i++) {
          Formal p = s.Method.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(s.Args[i]);
            sep = ", ";
          }
        }

        foreach (var outTmp in outTmps) {
          wr.Write("{0}out {1}", sep, outTmp);
          sep = ", ";
        }
        wr.WriteLine(");");

        // assign to the actual LHSs
        for (int j = 0; j < lvalues.Count; j++) {
          Indent(indent);
          wr.WriteLine("{0} = {1};", lvalues[j], outTmps[j]);
        }
      }
    }

    int tmpVarCount = 0;

    /// <summary>
    /// Before calling TrAssignmentRhs(rhs), the caller must have spilled the let variables declared in "rhs".
    /// </summary>
    void TrAssignmentRhs(AssignmentRhs rhs) {
      Contract.Requires(rhs != null);
      Contract.Requires(!(rhs is HavocRhs));
      if (rhs is ExprRhs) {
        ExprRhs e = (ExprRhs)rhs;
        TrExpr(e.Expr);

      } else {
        TypeRhs tp = (TypeRhs)rhs;
        if (tp.ArrayDimensions == null) {
          wr.Write("new {0}()", TypeName(tp.EType));
        } else {
          if (tp.EType is IntType || tp.EType.IsTypeParameter) {
            // Because the default constructor for BigInteger does not generate a valid BigInteger, we have
            // to excplicitly initialize the elements of an integer array.  This is all done in a helper routine.
            wr.Write("Dafny.Helpers.InitNewArray{0}<{1}>", tp.ArrayDimensions.Count, TypeName(tp.EType));
            string prefix = "(";
            foreach (Expression dim in tp.ArrayDimensions) {
              wr.Write(prefix);
              TrParenExpr(dim);
              prefix = ", ";
            }
            wr.Write(")");
          } else {
            wr.Write("new {0}", TypeName(tp.EType));
            string prefix = "[";
            foreach (Expression dim in tp.ArrayDimensions) {
              wr.Write("{0}(int)", prefix);
              TrParenExpr(dim);
              prefix = ", ";
            }
            wr.Write("]");
          }
        }
      }
    }

    void TrStmtList(List<Statement/*!*/>/*!*/ stmts, int indent) {Contract.Requires(cce.NonNullElements(stmts));
      foreach (Statement ss in stmts) {
        TrStmt(ss, indent + IndentAmount);
        if (ss.Labels != null) {
          Indent(indent);  // labels are not indented as much as the statements
          wr.WriteLine("after_{0}: ;", ss.Labels.Data.UniqueId);
        }
      }
    }

    void TrLocalVar(LocalVariable s, bool alwaysInitialize, int indent) {
      Contract.Requires(s != null);
      if (s.IsGhost) {
        // only emit non-ghosts (we get here only for local variables introduced implicitly by call statements)
        return;
      }

      Indent(indent);
      wr.Write("{0} @{1}", TypeName(s.Type), s.CompileName);
      if (alwaysInitialize) {
        // produce a default value
        wr.WriteLine(" = {0};", DefaultValue(s.Type));
      } else {
        wr.WriteLine(";");
      }
    }

    void MatchCasePrelude(string source, UserDefinedType sourceType, DatatypeCtor ctor, List<BoundVar/*!*/>/*!*/ arguments, int caseIndex, int caseCount, int indent) {
      Contract.Requires(source != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(ctor != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(0 <= indent);
      // if (source.is_Ctor0) {
      //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
      //   ...
      Indent(indent);
      wr.Write("{0}if (", caseIndex == 0 ? "" : "} else ");
      if (caseIndex == caseCount - 1) {
        wr.Write("true");
      } else {
        wr.Write("{0}.is_{1}", source, ctor.CompileName);
      }
      wr.WriteLine(") {");

      int k = 0;  // number of processed non-ghost arguments
      for (int m = 0; m < ctor.Formals.Count; m++) {
        Formal arg = ctor.Formals[m];
        if (!arg.IsGhost) {
          BoundVar bv = arguments[m];
          // FormalType f0 = ((Dt_Ctor0)source._D).a0;
          Indent(indent + IndentAmount);
          wr.WriteLine("{0} @{1} = (({2}){3}._D).@{4};",
            TypeName(bv.Type), bv.CompileName, DtCtorName(ctor, sourceType.TypeArgs), source, FormalName(arg, k));
          k++;
        }
      }
    }

    // ----- Expression ---------------------------------------------------------------------------

    /// <summary>
    /// Before calling TrParenExpr(expr), the caller must have spilled the let variables declared in "expr".
    /// </summary>
    void TrParenExpr(string prefix, Expression expr) {
      Contract.Requires(prefix != null);
      Contract.Requires(expr != null);
      wr.Write(prefix);
      TrParenExpr(expr);
    }

    /// <summary>
    /// Before calling TrParenExpr(expr), the caller must have spilled the let variables declared in "expr".
    /// </summary>
    void TrParenExpr(Expression expr) {
      Contract.Requires(expr != null);
      wr.Write("(");
      TrExpr(expr);
      wr.Write(")");
    }

    /// <summary>
    /// Before calling TrExprList(exprs), the caller must have spilled the let variables declared in expressions in "exprs".
    /// </summary>
    void TrExprList(List<Expression/*!*/>/*!*/ exprs) {
      Contract.Requires(cce.NonNullElements(exprs));
      wr.Write("(");
      string sep = "";
      foreach (Expression e in exprs) {
        wr.Write(sep);
        TrExpr(e);
        sep = ", ";
      }
      wr.Write(")");
    }
    void TrExprPairList(List<ExpressionPair/*!*/>/*!*/ exprs) {
      Contract.Requires(cce.NonNullElements(exprs));
      wr.Write("(");
      string sep = "";
      foreach (ExpressionPair p in exprs) {
        wr.Write(sep);
        wr.Write("new Dafny.Pair<");
        wr.Write(TypeName(p.A.Type));
        wr.Write(",");
        wr.Write(TypeName(p.B.Type));
        wr.Write(">(");
        TrExpr(p.A);
        wr.Write(",");
        TrExpr(p.B);
        wr.Write(")");
        sep = ", ";
      }
      wr.Write(")");
    }

    /// <summary>
    /// Before calling TrExpr(expr), the caller must have spilled the let variables declared in "expr".
    /// </summary>
    void TrExpr(Expression expr)
    {
      Contract.Requires(expr != null);
      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e.Value == null) {
          wr.Write("({0})null", TypeName(e.Type));
        } else if (e.Value is bool) {
          wr.Write((bool)e.Value ? "true" : "false");
        } else if (e.Value is BigInteger) {
          BigInteger i = (BigInteger)e.Value;
          if (new BigInteger(int.MinValue) <= i && i <= new BigInteger(int.MaxValue)) {
            wr.Write("new BigInteger({0})", i);
          } else {
            wr.Write("BigInteger.Parse(\"{0}\")", i);
          }
        } else if (e.Value is Basetypes.BigDec) {
          var n = (Basetypes.BigDec)e.Value;
          if (0 <= n.Exponent) {
            wr.Write("new Dafny.BigRational(new BigInteger({0}", n.Mantissa);
            for (int i = 0; i < n.Exponent; i++) {
              wr.Write("0");
            }
            wr.Write("), BigInteger.One)");
          } else {
            wr.Write("new Dafny.BigRational(new BigInteger({0}), new BigInteger(1", n.Mantissa);
            for (int i = n.Exponent; i < 0; i++) {
              wr.Write("0");
            }
            wr.Write("))");
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
        }

      } else if (expr is ThisExpr) {
        wr.Write(enclosingMethod != null && enclosingMethod.IsTailRecursive ? "_this" : "this");

      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        wr.Write("@" + e.Var.CompileName);

      } else if (expr is SetDisplayExpr) {
        SetDisplayExpr e = (SetDisplayExpr)expr;
        Type elType = cce.NonNull((SetType)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySetClass, TypeName(elType));
        TrExprList(e.Elements);

      } else if (expr is MultiSetDisplayExpr) {
        MultiSetDisplayExpr e = (MultiSetDisplayExpr)expr;
        Type elType = cce.NonNull((MultiSetType)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnyMultiSetClass, TypeName(elType));
        TrExprList(e.Elements);

      } else if (expr is SeqDisplayExpr) {
        SeqDisplayExpr e = (SeqDisplayExpr)expr;
        Type elType = cce.NonNull((SeqType)e.Type).Arg;
        wr.Write("{0}<{1}>.FromElements", DafnySeqClass, TypeName(elType));
        TrExprList(e.Elements);

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        wr.Write("{0}.FromElements", TypeName(e.Type));
        TrExprPairList(e.Elements);

      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        SpecialField sf = e.Field as SpecialField;
        if (sf != null) {
          wr.Write(sf.PreString);
          TrParenExpr(e.Obj);
          wr.Write(".@{0}", sf.CompiledName);
          wr.Write(sf.PostString);
        } else {
          TrParenExpr(e.Obj);
          wr.Write(".@{0}", e.Field.CompileName);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        Contract.Assert(e.Seq.Type != null);
        if (e.Seq.Type.IsArrayType) {
          if (e.SelectOne) {
            Contract.Assert(e.E0 != null && e.E1 == null);
            TrParenExpr(e.Seq);
            wr.Write("[(int)");
            TrParenExpr(e.E0);
            wr.Write("]");
          } else {
            TrParenExpr("Dafny.Helpers.SeqFromArray", e.Seq);
            if (e.E1 != null) {
              TrParenExpr(".Take", e.E1);
            }
            if (e.E0 != null) {
              TrParenExpr(".Drop", e.E0);
            }
          }
        } else if (e.SelectOne) {
          Contract.Assert(e.E0 != null && e.E1 == null);
          TrParenExpr(e.Seq);
          TrParenExpr(".Select", e.E0);
        } else {
          TrParenExpr(e.Seq);
          if (e.E1 != null) {
            TrParenExpr(".Take", e.E1);
          }
          if (e.E0 != null) {
            TrParenExpr(".Drop", e.E0);
          }
        }
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        wr.Write("{0}<{1}>", DafnyMultiSetClass, TypeName(((CollectionType)e.E.Type).Arg));
        if (e.E.Type is SeqType) {
          TrParenExpr(".FromSeq", e.E);
        } else if (e.E.Type is SetType) {
          TrParenExpr(".FromSet", e.E);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        TrParenExpr(e.Array);
        string prefix = "[";
        foreach (Expression idx in e.Indices) {
          wr.Write("{0}(int)", prefix);
          TrParenExpr(idx);
          prefix = ", ";
        }
        wr.Write("]");

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        if (e.ResolvedUpdateExpr != null)
        {
          TrExpr(e.ResolvedUpdateExpr);
        }
        else
        {
          TrParenExpr(e.Seq);
          wr.Write(".Update(");
          TrExpr(e.Index);
          wr.Write(", ");
          TrExpr(e.Value);
          wr.Write(")");
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        CompileFunctionCallExpr(e, wr, TrExpr);

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
        var typeParams = dtv.InferredTypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeNames(dtv.InferredTypeArgs));

        wr.Write("new {0}{1}(", DtName(dtv.Ctor.EnclosingDatatype), typeParams);
        if (!dtv.IsCoCall) {
          // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
          //   new Dt_Cons<T>( args )
          wr.Write("new {0}(", DtCtorName(dtv.Ctor, dtv.InferredTypeArgs));
          string sep = "";
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Formal formal = dtv.Ctor.Formals[i];
            if (!formal.IsGhost) {
              wr.Write(sep);
              TrExpr(dtv.Arguments[i]);
              sep = ", ";
            }
          }
          wr.Write(")");
        } else {
          // In the case of a co-recursive call, generate:
          //     new Dt__Lazy<T>( new Dt__Lazy<T>.ComputerComputer( LAMBDA )() )
          // where LAMBDA is:
          //     () => { var someLocals = eagerlyEvaluatedArguments;
          //             return () => { return Dt_Cons<T>( ...args...using someLocals and including function calls to be evaluated lazily... ); };
          //           }
          wr.Write("new {0}__Lazy{1}", dtv.DatatypeName, typeParams);
          wr.Write("(new {0}__Lazy{1}.ComputerComputer(() => {{ ", dtv.DatatypeName, typeParams);

          // locals
          string args = "";
          string sep = "";
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Formal formal = dtv.Ctor.Formals[i];
            if (!formal.IsGhost) {
              Expression actual = dtv.Arguments[i].Resolved;
              string arg;
              var fce = actual as FunctionCallExpr;
              if (fce == null || fce.CoCall != FunctionCallExpr.CoCallResolution.Yes) {
                string varName = "_ac" + tmpVarCount;
                tmpVarCount++;
                arg = varName;

                wr.Write("var {0} = ", varName);
                TrExpr(actual);
                wr.Write("; ");
              } else {
                var sw = new StringWriter();
                CompileFunctionCallExpr(fce, sw, (exp) => {
                  string varName = "_ac" + tmpVarCount;
                  tmpVarCount++;
                  sw.Write(varName);

                  wr.Write("var {0} = ", varName);
                  TrExpr(exp);
                  wr.Write("; ");

                });
                arg = sw.ToString();
              }
              args += sep + arg;
              sep = ", ";
            }
          }

          wr.Write("return () => { return ");

          wr.Write("new {0}({1}", DtCtorName(dtv.Ctor, dtv.InferredTypeArgs), args);
          wr.Write("); }; })())");
        }
        wr.Write(")");

      } else if (expr is OldExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // 'old' is always a ghost (right?)

      } else if (expr is FreshExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // 'fresh' is always a ghost

      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        switch (e.Op) {
          case UnaryExpr.Opcode.Not:
            wr.Write("!");
            TrParenExpr(e.E);
            break;
          case UnaryExpr.Opcode.SeqLength:
            if (cce.NonNull(e.E.Type).IsArrayType) {
              wr.Write("new BigInteger(");
              TrParenExpr(e.E);
              wr.Write(".Length)");
            } else {
              TrParenExpr(e.E);
              wr.Write(".Length");
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
        }

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        string opString = null;
        string preOpString = "";
        string callString = null;

        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Iff:
            opString = "==";  break;
          case BinaryExpr.ResolvedOpcode.Imp:
            preOpString = "!";  opString = "||";  break;
          case BinaryExpr.ResolvedOpcode.Or:
            opString = "||";  break;
          case BinaryExpr.ResolvedOpcode.And:
            opString = "&&";  break;

          case BinaryExpr.ResolvedOpcode.EqCommon: {
            Type t = cce.NonNull(e.E0.Type);
            if (t.IsDatatype || t.IsTypeParameter) {
              callString = "Equals";
            } else if (t.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "== (object)";
            } else {
              opString = "==";
            }
            break;
          }
          case BinaryExpr.ResolvedOpcode.NeqCommon: {
            Type t = cce.NonNull(e.E0.Type);
            if (t.IsDatatype || t.IsTypeParameter) {
              preOpString = "!";
              callString = "Equals";
            } else if (t.IsRefType) {
              // Dafny's type rules are slightly different C#, so we may need a cast here.
              // For example, Dafny allows x==y if x:array<T> and y:array<int> and T is some
              // type parameter.
              opString = "!= (object)";
            } else {
              opString = "!=";
            }
            break;
          }

          case BinaryExpr.ResolvedOpcode.Lt:
            opString = "<";  break;
          case BinaryExpr.ResolvedOpcode.Le:
            opString = "<=";  break;
          case BinaryExpr.ResolvedOpcode.Ge:
            opString = ">=";  break;
          case BinaryExpr.ResolvedOpcode.Gt:
            opString = ">";  break;
          case BinaryExpr.ResolvedOpcode.Add:
            opString = "+";  break;
          case BinaryExpr.ResolvedOpcode.Sub:
            opString = "-";  break;
          case BinaryExpr.ResolvedOpcode.Mul:
            opString = "*";  break;
          case BinaryExpr.ResolvedOpcode.Div:
            wr.Write("Dafny.Helpers.EuclideanDivision(");
            TrParenExpr(e.E0);
            wr.Write(", ");
            TrExpr(e.E1);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.Mod:
            wr.Write("Dafny.Helpers.EuclideanModulus(");
            TrParenExpr(e.E0);
            wr.Write(", ");
            TrExpr(e.E1);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.SetEq:
          case BinaryExpr.ResolvedOpcode.MultiSetEq:
          case BinaryExpr.ResolvedOpcode.SeqEq:
          case BinaryExpr.ResolvedOpcode.MapEq:
            callString = "Equals";  break;
          case BinaryExpr.ResolvedOpcode.SetNeq:
          case BinaryExpr.ResolvedOpcode.MultiSetNeq:
          case BinaryExpr.ResolvedOpcode.SeqNeq:
          case BinaryExpr.ResolvedOpcode.MapNeq:
            preOpString = "!";  callString = "Equals";  break;
          case BinaryExpr.ResolvedOpcode.ProperSubset:
          case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
            callString = "IsProperSubsetOf";  break;
          case BinaryExpr.ResolvedOpcode.Subset:
          case BinaryExpr.ResolvedOpcode.MultiSubset:
            callString = "IsSubsetOf";  break;
          case BinaryExpr.ResolvedOpcode.Superset:
          case BinaryExpr.ResolvedOpcode.MultiSuperset:
            callString = "IsSupersetOf";  break;
          case BinaryExpr.ResolvedOpcode.ProperSuperset:
          case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
            callString = "IsProperSupersetOf";  break;
          case BinaryExpr.ResolvedOpcode.Disjoint:
          case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          case BinaryExpr.ResolvedOpcode.MapDisjoint:
            callString = "IsDisjointFrom";  break;
          case BinaryExpr.ResolvedOpcode.InSet:
          case BinaryExpr.ResolvedOpcode.InMultiSet:
          case BinaryExpr.ResolvedOpcode.InMap:
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.NotInSet:
          case BinaryExpr.ResolvedOpcode.NotInMultiSet:
          case BinaryExpr.ResolvedOpcode.NotInMap:
            wr.Write("!");
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.Union:
          case BinaryExpr.ResolvedOpcode.MultiSetUnion:
            callString = "Union";  break;
          case BinaryExpr.ResolvedOpcode.Intersection:
          case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
            callString = "Intersect";  break;
          case BinaryExpr.ResolvedOpcode.SetDifference:
          case BinaryExpr.ResolvedOpcode.MultiSetDifference:
            callString = "Difference";  break;

          case BinaryExpr.ResolvedOpcode.ProperPrefix:
            callString = "IsProperPrefixOf";  break;
          case BinaryExpr.ResolvedOpcode.Prefix:
            callString = "IsPrefixOf";  break;
          case BinaryExpr.ResolvedOpcode.Concat:
            callString = "Concat";  break;
          case BinaryExpr.ResolvedOpcode.InSeq:
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;
          case BinaryExpr.ResolvedOpcode.NotInSeq:
            wr.Write("!");
            TrParenExpr(e.E1);
            wr.Write(".Contains(");
            TrExpr(e.E0);
            wr.Write(")");
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
        }
        if (opString != null) {
          wr.Write(preOpString);
          TrParenExpr(e.E0);
          wr.Write(" {0} ", opString);
          TrParenExpr(e.E1);
        } else if (callString != null) {
          wr.Write(preOpString);
          TrParenExpr(e.E0);
          wr.Write(".@{0}(", callString);
          TrExpr(e.E1);
          wr.Write(")");
        }

      } else if (expr is TernaryExpr) {
        Contract.Assume(false);  // currently, none of the ternary expressions is compilable

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        // The Dafny "let" expression
        //    var Pattern(x,y) := G; E
        // is translated into C# as:
        //    ExpressionSequence(tmp = G,
        //      ExpressionSequence(x = dtorX(tmp),
        //      ExpressionSequence(y = dtorY(tmp), E)))
        // preceded by the declaration of tmp, x, y.
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        Contract.Assert(e.Exact);  // because !Exact is ghost only
        var neededCloseParens = 0;
        for (int i = 0; i < e.LHSs.Count; i++) {
          var lhs = e.LHSs[i];
          if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
            var rhsName = string.Format("_pat_let{0}_{1}", GetUniqueAstNumber(e), i);
            wr.Write("Dafny.Helpers.ExpressionSequence({0} = ", rhsName);
            TrExpr(e.RHSs[i]);
            wr.Write(", ");
            neededCloseParens++;
            var c = TrCasePattern(lhs, rhsName);
            Contract.Assert(c != 0);  // we already checked that there's at least one non-ghost
            neededCloseParens += c;
          }
        }
        TrExpr(e.Body);
        for (int i = 0; i < neededCloseParens; i++) {
          wr.Write(")");
        }

      } else  if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        // new Dafny.Helpers.Function<SourceType, TargetType>(delegate (SourceType _source) {
        //   if (source.is_Ctor0) {
        //     FormalType f0 = ((Dt_Ctor0)source._D).a0;
        //     ...
        //     return Body0;
        //   } else if (...) {
        //     ...
        //   } else if (true) {
        //     ...
        //   }
        // }(src)

        string source = "_source" + tmpVarCount;
        tmpVarCount++;
        wr.Write("new Dafny.Helpers.Function<{0}, {1}>(delegate ({0} {2}) {{ ", TypeName(e.Source.Type), TypeName(e.Type), source);

        if (e.Cases.Count == 0) {
          // the verifier would have proved we never get here; still, we need some code that will compile
          wr.Write("throw new System.Exception();");
        } else {
          int i = 0;
          var sourceType = (UserDefinedType)e.Source.Type;
          foreach (MatchCaseExpr mc in e.Cases) {
            MatchCasePrelude(source, sourceType, cce.NonNull(mc.Ctor), mc.Arguments, i, e.Cases.Count, 0);
            wr.Write("return ");
            TrExpr(mc.Body);
            wr.Write("; ");
            i++;
          }
          wr.Write("}");
        }
        // We end with applying the source expression to the delegate we just built
        wr.Write("})(");
        TrExpr(e.Source);
        wr.Write(")");

      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.Bounds != null);  // for non-ghost quantifiers, the resolver would have insisted on finding bounds
        var n = e.BoundVars.Count;
        Contract.Assert(e.Bounds.Count == n);
        for (int i = 0; i < n; i++) {
          var bound = e.Bounds[i];
          var bv = e.BoundVars[i];
          // emit:  Dafny.Helpers.QuantX(boundsInformation, isForall, bv => body)
          if (bound is ComprehensionExpr.BoolBoundedPool) {
            wr.Write("Dafny.Helpers.QuantBool(");
          } else if (bound is ComprehensionExpr.IntBoundedPool) {
            var b = (ComprehensionExpr.IntBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantInt(");
            TrExpr(b.LowerBound);
            wr.Write(", ");
            TrExpr(b.UpperBound);
            wr.Write(", ");
          } else if (bound is ComprehensionExpr.SetBoundedPool) {
            var b = (ComprehensionExpr.SetBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantSet(");
            TrExpr(b.Set);
            wr.Write(", ");
          } else if (bound is ComprehensionExpr.MapBoundedPool) {
            var b = (ComprehensionExpr.MapBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantMap(");
            TrExpr(b.Map);
            wr.Write(", ");
          } else if (bound is ComprehensionExpr.SeqBoundedPool) {
            var b = (ComprehensionExpr.SeqBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantSeq(");
            TrExpr(b.Seq);
            wr.Write(", ");
          } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
            var b = (ComprehensionExpr.DatatypeBoundedPool)bound;
            wr.Write("Dafny.Helpers.QuantDatatype(");

            wr.Write("{0}.AllSingletonConstructors, ", DtName(b.Decl));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
          }
          wr.Write("{0}, ", expr is ForallExpr ? "true" : "false");
          wr.Write("@{0} => ", bv.CompileName);
        }
        TrExpr(e.LogicalBody());
        for (int i = 0; i < n; i++) {
          wr.Write(")");
        }

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        // For "set i,j,k,l | R(i,j,k,l) :: Term(i,j,k,l)" where the term has type "G", emit something like:
        // ((ComprehensionDelegate<G>)delegate() {
        //   var _coll = new List<G>();
        //   foreach (L l in sq.Elements) {
        //     foreach (K k in st.Elements) {
        //       for (BigInteger j = Lo; j < Hi; j++) {
        //         for (bool i in Helper.AllBooleans) {
        //           if (R(i,j,k,l)) {
        //             _coll.Add(Term(i,j,k,l));
        //           }
        //         }
        //       }
        //     }
        //   }
        //   return Dafny.Set<G>.FromCollection(_coll);
        // })()
        Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
        var typeName = TypeName(((SetType)e.Type).Arg);
        wr.Write("((Dafny.Helpers.ComprehensionDelegate<{0}>)delegate() {{ ", typeName);
        wr.Write("var _coll = new System.Collections.Generic.List<{0}>(); ", typeName);
        var n = e.BoundVars.Count;
        Contract.Assert(e.Bounds.Count == n);
        for (int i = 0; i < n; i++) {
          var bound = e.Bounds[i];
          var bv = e.BoundVars[i];
          if (bound is ComprehensionExpr.BoolBoundedPool) {
            wr.Write("foreach (var @{0} in Dafny.Helpers.AllBooleans) {{ ", bv.CompileName);
          } else if (bound is ComprehensionExpr.IntBoundedPool) {
            var b = (ComprehensionExpr.IntBoundedPool)bound;
            wr.Write("for (var @{0} = ", bv.CompileName);
            TrExpr(b.LowerBound);
            wr.Write("; @{0} < ", bv.CompileName);
            TrExpr(b.UpperBound);
            wr.Write("; @{0}++) {{ ", bv.CompileName);
          } else if (bound is ComprehensionExpr.SetBoundedPool) {
            var b = (ComprehensionExpr.SetBoundedPool)bound;
            wr.Write("foreach (var @{0} in (", bv.CompileName);
            TrExpr(b.Set);
            wr.Write(").Elements) { ");
          } else if (bound is ComprehensionExpr.MapBoundedPool) {
            var b = (ComprehensionExpr.MapBoundedPool)bound;
            wr.Write("foreach (var @{0} in (", bv.CompileName);
            TrExpr(b.Map);
            wr.Write(").Domain) { ");
          } else if (bound is ComprehensionExpr.SeqBoundedPool) {
            var b = (ComprehensionExpr.SeqBoundedPool)bound;
            wr.Write("foreach (var @{0} in (", bv.CompileName);
            TrExpr(b.Seq);
            wr.Write(").Elements) { ");
          } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
            var b = (ComprehensionExpr.DatatypeBoundedPool)bound;
            wr.Write("foreach (var @{0} in {1}.AllSingletonConstructors) {{", bv.CompileName, TypeName(bv.Type));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
          }
        }
        wr.Write("if (");
        TrExpr(e.Range);
        wr.Write(") { _coll.Add(");
        TrExpr(e.Term);
        wr.Write("); }");
        for (int i = 0; i < n; i++) {
          wr.Write("}");
        }
        wr.Write("return Dafny.Set<{0}>.FromCollection(_coll); ", typeName);
        wr.Write("})()");

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        // For "map i | R(i) :: Term(i)" where the term has type "V" and i has type "U", emit something like:
        // ((MapComprehensionDelegate<U, V>)delegate() {
        //   var _coll = new List<Pair<U,V>>();
        //   foreach (L l in sq.Elements) {
        //     foreach (K k in st.Elements) {
        //       for (BigInteger j = Lo; j < Hi; j++) {
        //         for (bool i in Helper.AllBooleans) {
        //           if (R(i,j,k,l)) {
        //             _coll.Add(new Pair(i, Term(i));
        //           }
        //         }
        //       }
        //     }
        //   }
        //   return Dafny.Map<U, V>.FromElements(_coll);
        // })()
        Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
        var domtypeName = TypeName(((MapType)e.Type).Domain);
        var rantypeName = TypeName(((MapType)e.Type).Range);
        wr.Write("((Dafny.Helpers.MapComprehensionDelegate<{0},{1}>)delegate() {{ ", domtypeName, rantypeName);
        wr.Write("var _coll = new System.Collections.Generic.List<Dafny.Pair<{0},{1}>>(); ", domtypeName, rantypeName);
        var n = e.BoundVars.Count;
        Contract.Assert(e.Bounds.Count == n && n == 1);
        var bound = e.Bounds[0];
        var bv = e.BoundVars[0];
        if (bound is ComprehensionExpr.BoolBoundedPool) {
          wr.Write("foreach (var @{0} in Dafny.Helpers.AllBooleans) {{ ", bv.CompileName);
        } else if (bound is ComprehensionExpr.IntBoundedPool) {
          var b = (ComprehensionExpr.IntBoundedPool)bound;
          wr.Write("for (var @{0} = ", bv.CompileName);
          TrExpr(b.LowerBound);
          wr.Write("; @{0} < ", bv.CompileName);
          TrExpr(b.UpperBound);
          wr.Write("; @{0}++) {{ ", bv.CompileName);
        } else if (bound is ComprehensionExpr.SetBoundedPool) {
          var b = (ComprehensionExpr.SetBoundedPool)bound;
          wr.Write("foreach (var @{0} in (", bv.CompileName);
          TrExpr(b.Set);
          wr.Write(").Elements) { ");
        } else if (bound is ComprehensionExpr.MapBoundedPool) {
          var b = (ComprehensionExpr.MapBoundedPool)bound;
          wr.Write("foreach (var @{0} in (", bv.CompileName);
          TrExpr(b.Map);
          wr.Write(").Domain) { ");
        } else if (bound is ComprehensionExpr.SeqBoundedPool) {
          var b = (ComprehensionExpr.SeqBoundedPool)bound;
          wr.Write("foreach (var @{0} in (", bv.CompileName);
          TrExpr(b.Seq);
          wr.Write(").Elements) { ");
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected BoundedPool type
        }
        wr.Write("if (");
        TrExpr(e.Range);
        wr.Write(") { ");
        wr.Write("_coll.Add(new Dafny.Pair<{0},{1}>(@{2},", domtypeName, rantypeName, bv.CompileName);
        TrExpr(e.Term);
        wr.Write(")); }");
        wr.Write("}");
        wr.Write("return Dafny.Map<{0},{1}>.FromCollection(_coll); ", domtypeName, rantypeName);
        wr.Write("})()");

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        TrExpr(e.E);

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        wr.Write("(");
        TrExpr(e.Test);
        wr.Write(") ? (");
        TrExpr(e.Thn);
        wr.Write(") : (");
        TrExpr(e.Els);
        wr.Write(")");

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        TrExpr(e.ResolvedExpression);

      } else if (expr is NamedExpr) {
        TrExpr(((NamedExpr)expr).Body);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    int TrCasePattern(CasePattern pat, string rhsName) {
      Contract.Requires(pat != null);
      Contract.Requires(rhsName != null);
      int c = 0;
      if (pat.Var != null) {
        var bv = pat.Var;
        if (!bv.IsGhost) {
          wr.Write("Dafny.Helpers.ExpressionSequence(@{0} = {1}, ", bv.CompileName, rhsName);
          c++;
        }
      } else if (pat.Arguments != null) {
        var ctor = pat.Ctor;
        Contract.Assert(ctor != null);  // follows from successful resolution
        Contract.Assert(pat.Arguments.Count == ctor.Formals.Count);  // follows from successful resolution
        var k = 0;  // number of non-ghost formals processed
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var formal = ctor.Formals[i];
          if (formal.IsGhost) {
            // nothing to compile, but do a sanity check
            Contract.Assert(!Contract.Exists(arg.Vars, bv => !bv.IsGhost));
          } else {
            c += TrCasePattern(arg, string.Format("(({0})({1})._D).@{2}", DtCtorName(ctor, ((DatatypeValue)pat.Expr).InferredTypeArgs), rhsName, FormalName(formal, k)));
            k++;
          }
        }
      }
      return c;
    }

    delegate void FCE_Arg_Translator(Expression e);

    void CompileFunctionCallExpr(FunctionCallExpr e, TextWriter twr, FCE_Arg_Translator tr) {
      Function f = cce.NonNull(e.Function);
      if (f.IsStatic) {
        twr.Write(TypeName(cce.NonNull(e.Receiver.Type)));
      } else {
        twr.Write("(");
        tr(e.Receiver);
        twr.Write(")");
      }
      twr.Write(".@{0}", f.CompileName);
      twr.Write("(");
      string sep = "";
      for (int i = 0; i < e.Args.Count; i++) {
        if (!e.Function.Formals[i].IsGhost) {
          twr.Write(sep);
          tr(e.Args[i]);
          sep = ", ";
        }
      }
      twr.Write(")");
    }
  }
}
